-- Prove2me | Theorems.Thm_KellyStochasticNetworks_MigrationDynamics_open_migration_time_reversal
-- name    : KellyStochasticNetworks.MigrationDynamics.open_migration_time_reversal
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-22T03:47:23.767916+00:00
-- url     : https://prove2.me/theorems/dc6cb4fc-ed27-4bb6-ad6c-a1227f65af61
-- title:
--   Theorem 2.9 — stationary open migration processes under time reversal
-- statement:
--   Let $(n(t))_{t\in\mathbb R}$ be a stationary open migration process with a finite positive number $J$ of colonies and state space $\mathbb N^J$. Its transitions move one individual between distinct colonies, remove one from a nonempty colony, or add one from outside, with the rate factors of Section 2.4. The process is irreducible and nonexplosive, with strictly positive finite exit rates, as required throughout the source. Then
--   $$\bigl(n(-t)\bigr)_{t\in\mathbb R}\quad\text{is a stationary open migration process}.$$
--   Thus reversing the actual stationary random process preserves the class of open migration processes. The resulting rates need not equal the original rates.
--
--   **Formalization Note** The hypothesis does not assume a product-form equilibrium law, finite normalizers, or any conclusion about the reversed process. It asserts existence of admissible migration rate data and a positive normalized stationary law. The conclusion asserts these properties for $t\mapsto n(-t)$ on the same probability space. The endpoint convention is allowed to reverse at jumps. Dependency declarations are quoted verbatim in Lean comments for blind inspection.
-- source:
--   Kelly & Yudovina, Stochastic Networks (2014), supplied Lecture Notes PDF, printed p. 32 (PDF p. 40), Theorem 2.9; proof printed p. 33 (PDF p. 41)

import Definitions.Def_KellyStochasticNetworks_MigrationDynamics_OpenProcess

open MeasureTheory

/- BEGIN IMPORTED DEFINITIONS FOR BLIND AUDIT
The following are the exact declarations from the imported modules, with comments omitted.
They are quoted here only to expose dependencies to the tool-free auditor.

namespace KellyStochasticNetworks


def Tjk {J : ℕ} (j k : Fin J) (n : Fin J → ℕ) : Fin J → ℕ := fun i =>
  if i = j then n j - 1 else if i = k then n k + 1 else n i


def Tout {J : ℕ} (j : Fin J) (n : Fin J → ℕ) : Fin J → ℕ := fun i =>
  if i = j then n j - 1 else n i


def Tin {J : ℕ} (k : Fin J) (n : Fin J → ℕ) : Fin J → ℕ := fun i =>
  if i = k then n k + 1 else n i


def phiProd {J : ℕ} (φ : Fin J → ℕ → ℝ) (j : Fin J) (m : ℕ) : ℝ :=
  ∏ r ∈ Finset.Icc 1 m, φ j r


noncomputable def closedMigrationRates {J : ℕ} (lam : Fin J → Fin J → ℝ) (φ : Fin J → ℕ → ℝ) :
    (Fin J → ℕ) → (Fin J → ℕ) → ℝ := fun n m =>
  ∑ j, ∑ k, if m = Tjk j k n then lam j k * φ j (n j) else 0


noncomputable def openMigrationRates {J : ℕ} (lam : Fin J → Fin J → ℝ) (mu nu : Fin J → ℝ)
    (φ : Fin J → ℕ → ℝ) : (Fin J → ℕ) → (Fin J → ℕ) → ℝ := fun n m =>
  closedMigrationRates lam φ n m
    + (∑ j, if m = Tout j n then mu j * φ j (n j) else 0)
    + (∑ k, if m = Tin k n then nu k else 0)


def ClosedTraffic {J : ℕ} (lam : Fin J → Fin J → ℝ) (α : Fin J → ℝ) : Prop :=
  (∀ j, 0 < α j) ∧ (∑ j, α j = 1) ∧ ∀ j, α j * ∑ k, lam j k = ∑ k, α k * lam k j


def OpenTraffic {J : ℕ} (lam : Fin J → Fin J → ℝ) (mu nu α : Fin J → ℝ) : Prop :=
  ∀ j, α j * (mu j + ∑ k, lam j k) = nu j + ∑ k, α k * lam k j


noncomputable def migrationMarginal {J : ℕ} (α g : Fin J → ℝ) (φ : Fin J → ℕ → ℝ)
    (j : Fin J) (m : ℕ) : ℝ := (g j)⁻¹ * (α j ^ m / phiProd φ j m)


noncomputable def openMigrationPi {J : ℕ} (α g : Fin J → ℝ) (φ : Fin J → ℕ → ℝ)
    (n : Fin J → ℕ) : ℝ := ∏ j, migrationMarginal α g φ j (n j)


noncomputable def mm1Rates (lam mu : ℝ) : ℕ → ℕ → ℝ := fun j k =>
  if k = j + 1 then lam else if j = k + 1 then mu else 0


noncomputable def occupancy {N : ℕ} (a d : Fin N → ℝ) (s : ℝ) : ℝ :=
  ∑ i, Set.indicator (Set.Ico (a i) (d i)) (fun _ => (1 : ℝ)) s

end KellyStochasticNetworks

namespace KellyStochasticNetworks.MigrationDynamics


def LocallyFiniteJumpPath {S : Type*} (x : ℝ → S) : Prop :=
  (∀ a b : ℝ, a < b → ∃ D : Finset ℝ,
    ∀ s t : ℝ, a ≤ s → s ≤ t → t ≤ b →
      (∀ d ∈ D, d ∉ Set.Icc s t) → x s = x t) ∧
  ∀ t : ℝ, ∃ ε : ℝ, 0 < ε ∧
    ((∀ u ∈ Set.Ico t (t + ε), x u = x t) ∨
     (∀ u ∈ Set.Ioc (t - ε) t, x u = x t))


noncomputable def cylinder {Ω S : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℝ → Ω → S) {n : ℕ}
    (t : Fin n → ℝ) (x : Fin n → S) : ℝ :=
  (P {ω | ∀ i, X (t i) ω = x i}).toReal


def IsMarkovProcess {Ω S : Type*} [MeasurableSpace Ω]
    [MeasurableSpace S] [MeasurableSingletonClass S] [Countable S] [DecidableEq S]
    (P : Measure Ω) (X : ℝ → Ω → S) (q : S → S → ℝ) : Prop :=
  IsProbabilityMeasure P ∧
  (∀ t, Measurable (X t)) ∧
  (∀ᵐ ω ∂P, LocallyFiniteJumpPath (fun t => X t ω)) ∧
  (∀ i j, 0 ≤ q i j) ∧ (∀ i, q i i = 0) ∧
  (∀ i, Summable (q i) ∧ 0 < ∑' j, q i j) ∧
  (∀ i j, Relation.ReflTransGen (fun a b => 0 < q a b) i j) ∧
  ∃ K : ℝ → S → S → ℝ,
    (∀ h, 0 ≤ h → ∀ i, (∀ j, 0 ≤ K h i j) ∧ HasSum (K h i) 1) ∧
    (∀ i j, K 0 i j = if i = j then 1 else 0) ∧
    (∀ (n : ℕ) (t : Fin (n + 1) → ℝ) (x : Fin (n + 1) → S)
        (u : ℝ) (y : S), StrictMono t → t (Fin.last n) < u →
      (P {ω | (∀ i, X (t i) ω = x i) ∧ X u ω = y}).toReal =
        cylinder P X t x * K (u - t (Fin.last n)) (x (Fin.last n)) y) ∧
    (∀ i j, Tendsto
      (fun h : ℝ => (K h i j - if i = j then 1 else 0) / h)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (if i = j then -(∑' k, q i k) else q i j)))


def HasStationaryLaw {Ω S : Type*} [MeasurableSpace Ω]
    [MeasurableSpace S] [MeasurableSingletonClass S] [Countable S]
    (P : Measure Ω) (X : ℝ → Ω → S) (π : S → ℝ) : Prop :=
  IsProbabilityMeasure P ∧ (∀ t, Measurable (X t)) ∧
  (∀ i, 0 < π i) ∧ HasSum π 1 ∧
  ∀ t i, (P {ω | X t ω = i}).toReal = π i

end KellyStochasticNetworks.MigrationDynamics

namespace KellyStochasticNetworks.MigrationDynamics


structure MigrationData (J : ℕ) where
  lam : Fin J → Fin J → ℝ
  mu : Fin J → ℝ
  nu : Fin J → ℝ
  phi : Fin J → ℕ → ℝ
  lam_nonneg : ∀ j k, 0 ≤ lam j k
  lam_diag : ∀ j, lam j j = 0
  mu_nonneg : ∀ j, 0 ≤ mu j
  nu_nonneg : ∀ j, 0 ≤ nu j
  phi_zero : ∀ j, phi j 0 = 0
  phi_pos : ∀ j r, 0 < r → 0 < phi j r


noncomputable def MigrationData.rate {J : ℕ} (M : MigrationData J) :=
  KellyStochasticNetworks.openMigrationRates M.lam M.mu M.nu M.phi


def IsStationaryOpenMigration {Ω : Type*} [MeasurableSpace Ω] {J : ℕ}
    (P : Measure Ω) (X : ℝ → Ω → (Fin J → ℕ)) : Prop :=
  0 < J ∧ ∃ M : MigrationData J, ∃ π : (Fin J → ℕ) → ℝ,
    IsMarkovProcess P X M.rate ∧ HasStationaryLaw P X π

end KellyStochasticNetworks.MigrationDynamics
END IMPORTED DEFINITIONS FOR BLIND AUDIT -/

namespace KellyStochasticNetworks.MigrationDynamics

theorem open_migration_time_reversal {Ω : Type*} [MeasurableSpace Ω] {J : ℕ}
    (P : Measure Ω) (X : ℝ → Ω → (Fin J → ℕ))
    (hX : IsStationaryOpenMigration P X) :
    IsStationaryOpenMigration P (fun t => X (-t)) := by sorry

end KellyStochasticNetworks.MigrationDynamics
