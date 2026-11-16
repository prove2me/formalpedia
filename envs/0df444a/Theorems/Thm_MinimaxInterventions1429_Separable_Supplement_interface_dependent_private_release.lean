-- Prove2me | Theorems.Thm_MinimaxInterventions1429_Separable_Supplement_interface_dependent_private_release
-- name    : MinimaxInterventions1429.Separable.Supplement.interface_dependent_private_release
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T09:19:45.416006+00:00
-- url     : https://prove2.me/theorems/dedf28d5-9556-46a6-bccb-8d78a40c5a9f
-- title:
--   Theorem 6.5 — Interface-dependent private release equivalence
-- statement:
--   For any public group design and any nonempty compact public controls $K$ with norm bound $\tau$, put $\Lambda_K=\max_{C\in K}\Lambda(L_\theta(0)+C)$. Symmetry is not required. For every $\varepsilon\ge0$, $\delta,\beta\in[0,1)$,
--   $$\min\{\Lambda_K/8,\mathrm{err}_A/6\}\le\mathrm{dec}_{A,K}\le\min\{\Lambda_K,\mathrm{err}_A\}.$$
--   The lower reduction selects one public maximizing control $C^\star$ independently of the labels. For each $T\ge1$ and any private synopsis with tolerance $\alpha<\Lambda_K/8$, it makes exactly $(m-1)T$ threshold-bit calls, all of the form $C^\star+D_\tau B$ with $B\in S$. Its total centered release has error at most $6\alpha+3D_\tau2^{-T}$, with unchanged privacy and failure probability. This retains the finite-precision and single-control content behind the limiting error inequality.
--
--   Differences from the source:
--   - encoding: one-control lower reduction → a public maximizing control, literal known-contrast program, exact count and finite release bound; reason: the finite 6 alpha + 3 D_tau 2^(-T) guarantee is stated before the source limit
--   - encoding: m and k indexed from 1, with m,k >= 2 → Fin m and Fin k indexed from 0, with explicit nonzero instances and m,k >= 2; reason: source column 1 is Lean column 0; dimensions and closed-simplex boundary instances are preserved
-- source:
--   chaomeng chen, STOC 2027 submission #1429 (October 2026), Theorem 6.5, printed p.21 (PDF p.23)

import Definitions.Def_MinimaxInterventions1429_Separable_Supplement_Groups
set_option autoImplicit false
universe u_interface_dependent_private_release

noncomputable section

namespace MinimaxInterventions1429.Separable.Supplement
open MeasureTheory

theorem interface_dependent_private_release
    {N m : ℕ} [NeZero m] (hm : 2 ≤ m) (d : GroupDesign N m)
    (K : Set (Table m 2)) (τ : ℝ) (hK : ControlSet K τ)
    (ε δ β : ℝ) (hε : 0 ≤ ε) (hδ : 0 ≤ δ ∧ δ < 1) (hβ : 0 ≤ β ∧ β < 1) :
    (min (attainableInteraction d K / 8) (centeredReleaseError d ε δ β / 6) ≤
      decisionError replacement d.table (controlQueries K τ) ε δ β ∧
      decisionError replacement d.table (controlQueries K τ) ε δ β ≤
        min (attainableInteraction d K) (centeredReleaseError d ε δ β)) ∧
    ∃ C ∈ K, interaction (d.table (fun _ => false)+C) = attainableInteraction d K ∧
      ∀ (S : Type) [MeasurableSpace S] (syn : Synopsis S m 2)
        (law : Labels N → Measure S) (α : ℝ) (T : ℕ),
        0 ≤ α → α < attainableInteraction d K / 8 → 1 ≤ T →
        PrivateSynopsis replacement d.table (controlQueries K τ) ε δ β α syn law →
        (shiftProgram C τ (knownAlignment (α/dilation τ) T
          (contrasts (normalized (d.table (fun _ => false)) C τ)))).maxQueries = (m-1)*T ∧
        (shiftProgram C τ (knownAlignment (α/dilation τ) T
          (contrasts (normalized (d.table (fun _ => false)) C τ)))).queriesSatisfy
            (fun q => ∃ B, Allowed B ∧ q.surcharge = C+dilation τ • B) ∧
        Measurable (knownCenteredOutput d syn.decode C τ α T) ∧
        (let out := fun y => (law y).map (knownCenteredOutput d syn.decode C τ α T)
         (∀ y, IsProbabilityMeasure (out y)) ∧ DifferentiallyPrivate replacement ε δ out ∧
           centeredAccurate d out β (6*α+3*dilation τ*eta T)) := by sorry

end MinimaxInterventions1429.Separable.Supplement
