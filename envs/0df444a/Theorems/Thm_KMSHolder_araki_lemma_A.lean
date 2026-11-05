-- Prove2me | Theorems.Thm_KMSHolder_araki_lemma_A
-- name    : KMSHolder.araki_lemma_A
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:41:44.378437+00:00
-- url     : https://prove2.me/theorems/aeb012f8-f5b8-4dc2-b30b-88d4634a7fc0
-- title:
--   Araki's estimate (8) for chains of relative modular operators $\Delta^{z_j}_{\phi_j,\Omega}$
-- statement:
--   Let $M$ be a von Neumann algebra on $H$ with cyclic and separating unit vector $\Omega$. Let $n \ge 1$, $1 \le m \le n$, $z = (z_1, \dots, z_n) \in I^{(n)}$ (so $\Re z_j \ge 0$ and $\sum_j \Re z_j \le 1$), and let $z'_m, z''_m \in \mathbb C$ with $\Re z'_m, \Re z''_m > 0$, $z'_m + z''_m = z_m$ and
--
--   $$
--   \Re z_1 + \dots + \Re z_{m-1} + \Re z''_m \le \tfrac12, \qquad (6)
--   $$
--   $$
--   \Re z_n + \dots + \Re z_{m+1} + \Re z'_m \le \tfrac12. \qquad (7)
--   $$
--
--   Let $\phi_1, \dots, \phi_n$ be positive normal functionals on $M$ with relative modular operators $\Delta_{\phi_j,\Omega}$, and $X_0, \dots, X_n \in M$. Then the vectors
--
--   $$
--   R = \Delta^{z''_m}_{\phi_m,\Omega} X_{m-1} \Delta^{z_{m-1}}_{\phi_{m-1},\Omega} \cdots \Delta^{z_1}_{\phi_1,\Omega} X_0 \Omega,
--   \qquad
--   L = \Delta^{\bar z'_m}_{\phi_m,\Omega} X_m^* \Delta^{\bar z_{m+1}}_{\phi_{m+1},\Omega} \cdots \Delta^{\bar z_n}_{\phi_n,\Omega} X_n^* \Omega
--   $$
--
--   exist, each operator being applied to a vector in its domain, and
--
--   $$
--   |\langle L, R\rangle| \le \Big(\prod_{j=0}^n \|X_j\|\Big)\, \langle\Omega, \mathbb 1\Omega\rangle^{z_0} \prod_{j=1}^n \phi_j(\mathbb 1)^{\Re z_j}, \qquad z_0 = 1 - \sum_{j=1}^n \Re z_j. \qquad (8)
--   $$
--
--   This is Araki's Lemma A in Araki–Masuda, quoted in the paper as the key estimate of the proof of the Hölder inequality. Formally, $\langle L, R\rangle$ is $\omega(X_n \Delta^{z_n}_{\phi_n,\Omega} \cdots X_m \Delta^{z_m}_{\phi_m,\Omega} X_{m-1} \cdots \Delta^{z_1}_{\phi_1,\Omega} X_0)$. The factor $\langle\Omega, \mathbb 1\Omega\rangle^{z_0}$ equals $1$ since $\|\Omega\| = 1$.
--
--   **Formalization Note** The families $z, \phi, \Delta_{\phi_j,\Omega}, X$ are indexed by $\mathbb N$ with the paper's numbering; values at other indices are never used. The inner product is linear in the second entry, as in the paper (its footnote 3) and in Mathlib.
--
--   Differences from the source:
--   - reading: "$\Delta^{z_{j-1}}_{\phi_{m-1},\Omega}$" in the right vector → $\Delta^{z_{m-1}}_{\phi_{m-1},\Omega}$; reason: misprint; the operators of the right vector carry the indices $1, \dots, m-1$, matching $\phi_{m-1}$ and $X_{m-1}$.
--   - reading: the inner product of the two iterated expressions → both vectors exist step by step (each intermediate vector in the domain of the next power) and the bound holds for them; reason: the left-hand side of (8) presupposes the vectors exist; Araki's lemma asserts it.
--   - encoding: $\Delta_{\phi,\Omega} = S^*_{\phi,\Omega}\overline{S_{\phi,\Omega}}$ and its powers → any $T$ with `IsRelModular S φ T` and `posPowGraph`, with $T^z = 0$ on $\ker T$; reason: the characterization determines $\Delta_{\phi,\Omega}$ uniquely, and the support convention is Araki–Masuda's for non-faithful $\phi$.
--   - encoding: $M$ in standard form with cyclic separating $\Omega$; $M^+_*$; indices → `StandardModularData` (unit $\Omega$); `IsPosNormal`; $\mathbb N$-indexed families with the paper's numbering; reason: Lean convention; same instances.
-- source:
--   Jäkel–Robl, The Hölder Inequality for KMS States, arXiv:1103.3608v2, §3.1, eqs. (5)–(8), p.5 (Araki [3, Lemma A])

import Mathlib
import Definitions.Def_BoundedRecovery
import Definitions.Def_HollandsSanders_CFTBound_Entanglement
import Definitions.Def_KMSHolder_relIter
import Definitions.Def_KMSHolder_PosSpectralCalculus
import Definitions.Def_KMSHolder_posPowGraph
import Definitions.Def_KMSHolder_IsRelModular

open OAI.BoundedRecovery HollandsSanders.CFTBound
open scoped InnerProductSpace

namespace KMSHolder

/-- Jäkel–Robl, arXiv:1103.3608v2, §3.1, eqs. (5)–(8), p.5 (Araki [3, Lemma A], the key estimate
of the proof of Theorem 2.2). Let `z ∈ I⁽ⁿ⁾`, `1 ≤ m ≤ n`, and `z′ₘ, z″ₘ ∈ ℂ` with
`ℜz′ₘ, ℜz″ₘ > 0`, `z′ₘ + z″ₘ = zₘ`,
`ℜz₁ + ⋯ + ℜz_{m−1} + ℜz″ₘ ≤ 1/2` (6) and `ℜzₙ + ⋯ + ℜz_{m+1} + ℜz′ₘ ≤ 1/2` (7).
Then for `φ₁, …, φₙ ∈ M⁺_*` and `X₀, …, Xₙ ∈ M`,
`|(Δ^{z̄′ₘ}_{φₘ,Ω} X*ₘ Δ^{z̄ₘ₊₁}_{φₘ₊₁,Ω} ⋯ Δ^{z̄ₙ}_{φₙ,Ω} X*ₙ Ω,
   Δ^{z″ₘ}_{φₘ,Ω} X_{m−1} Δ^{z_{m−1}}_{φ_{m−1},Ω} ⋯ Δ^{z₁}_{φ₁,Ω} X₀ Ω)|
 ≤ (∏_{j=0}^n ‖Xⱼ‖) (Ω, 1Ω)^{z₀} (∏_{j=1}^n φⱼ(1)^{ℜzⱼ})`, with `z₀ = 1 − Σⱼ ℜzⱼ`.

The conclusion has two parts: (a) both vectors exist, every step lying in the domain of the next
relative modular power (`rightVecs`, `leftVecs` nonempty); (b) the bound holds for them.

**Formalization Note.**
* Indices are the paper's: `z j`, `φ j`, `T j` for `j = 1, …, n`, `X j` for `j = 0, …, n`
  (families on `ℕ`; values at other indices are never used).
* `T j` is any operator with `IsRelModular S (φ j) (T j)`, i.e. `Δ_{φⱼ,Ω}` (unique); powers
  follow the support convention `0^z = 0` on the kernel (`posPowGraph`).
* The printed `Δ^{z_{j−1}}_{φ_{m−1},Ω}` is read as `Δ^{z_{m−1}}_{φ_{m−1},Ω}` (misprint).
* The inner product is linear in the second entry, as in the paper (footnote 3) and Mathlib.
* `(Ω, 1Ω)^{z₀}` is kept literally (it equals `1` since `‖Ω‖ = 1`); `M⁺_*` is `IsPosNormal`.
* The right vector: `X₀Ω`, then for `j = 1, …, m−1` apply `Δ^{zⱼ}_{φⱼ,Ω}` and `Xⱼ`, then
  `Δ^{z″ₘ}_{φₘ,Ω}`. The left vector: `X*ₙΩ`, then for `j = n, …, m+1` apply `Δ^{z̄ⱼ}_{φⱼ,Ω}` and
  `X*_{j−1}`, then `Δ^{z̄′ₘ}_{φₘ,Ω}`. -/
theorem araki_lemma_A {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (S : StandardModularData H) (n m : ℕ) (hm1 : 1 ≤ m) (hmn : m ≤ n)
    (z : ℕ → ℂ) (hz_nonneg : ∀ j ∈ Finset.Icc 1 n, 0 ≤ (z j).re)
    (hz_sum : ∑ j ∈ Finset.Icc 1 n, (z j).re ≤ 1)
    (z' z'' : ℂ) (hz' : 0 < z'.re) (hz'' : 0 < z''.re) (hsplit : z' + z'' = z m)
    (h6 : ∑ j ∈ Finset.Ico 1 m, (z j).re + z''.re ≤ 1 / 2)
    (h7 : ∑ j ∈ Finset.Ioc m n, (z j).re + z'.re ≤ 1 / 2)
    (φ : ℕ → (H →L[ℂ] H) → ℂ)
    (hφ : ∀ j ∈ Finset.Icc 1 n, IsPosNormal (S.M : Set (H →L[ℂ] H)) (φ j))
    (T : ℕ → PosSpectralCalculus H) (hT : ∀ j ∈ Finset.Icc 1 n, IsRelModular S (φ j) (T j))
    (X : ℕ → H →L[ℂ] H) (hX : ∀ j ∈ Finset.range (n + 1), X j ∈ S.M) :
    let rightSteps : ℕ → Set (H × H) := fun i =>
      {q | ∃ w : H, (q.1, w) ∈ posPowGraph (T (i + 1)) (z (i + 1)) ∧ q.2 = X (i + 1) w}
    let rightVecs : Set H :=
      {R | ∃ x ∈ relIter rightSteps (m - 1) (X 0 S.xi), (x, R) ∈ posPowGraph (T m) z''}
    let leftSteps : ℕ → Set (H × H) := fun i =>
      {q | ∃ w : H, (q.1, w) ∈ posPowGraph (T (n - i)) (starRingEnd ℂ (z (n - i))) ∧
        q.2 = star (X (n - i - 1)) w}
    let leftVecs : Set H :=
      {L | ∃ x ∈ relIter leftSteps (n - m) (star (X n) S.xi),
        (x, L) ∈ posPowGraph (T m) (starRingEnd ℂ z')}
    rightVecs.Nonempty ∧ leftVecs.Nonempty ∧
      ∀ R ∈ rightVecs, ∀ L ∈ leftVecs,
        ‖⟪L, R⟫_ℂ‖ ≤ (∏ j ∈ Finset.range (n + 1), ‖X j‖) *
          (⟪S.xi, (1 : H →L[ℂ] H) S.xi⟫_ℂ).re ^ (1 - ∑ j ∈ Finset.Icc 1 n, (z j).re) *
          ∏ j ∈ Finset.Icc 1 n, (φ j 1).re ^ (z j).re := by sorry

end KMSHolder
