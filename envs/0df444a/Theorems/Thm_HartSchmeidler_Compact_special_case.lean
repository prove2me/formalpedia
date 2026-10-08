-- Prove2me | Theorems.Thm_HartSchmeidler_Compact_special_case
-- name    : HartSchmeidler.Compact.special_case
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T12:14:34.923134+00:00
-- url     : https://prove2.me/theorems/67ab1661-db40-4433-97ed-fa2f3d4784aa
-- title:
--   Proof of Theorem 3, pp. 24–25 — the special case: (4) for a deviation that is constant on a Borel set
-- statement:
--   Assume the hypotheses of Theorem 3: $N$ is a nonempty set of players, each $S^i$ is a nonempty compact Hausdorff space with its Borel σ-algebra, $S=\prod_jS^j$ carries the product topology and its Borel σ-algebra, and each payoff $h^i:S\to\mathbb R$ is continuous. Fix a profile $\hat s$, and for every f-set $T$ containing $\hat s$ let $q_T=\sum_{s\in F_T}w_T(s)\,\delta_s$ be a correlated equilibrium of the finite game $\Gamma_T$. Let $p$ be a regular probability measure on $S$ that is a cluster point of the net $(q_T)$ against continuous functions: for every continuous $f:S\to\mathbb R$, every $\varepsilon>0$ and every f-set $T_0\ni\hat s$ there is an f-set $T\supseteq T_0$ with $\hat s\in T$ and
--   $$
--   \Bigl|\int_S f\,dp-\sum_{s\in F_T}w_T(s)f(s)\Bigr|<\varepsilon .
--   $$
--   Let $i$ be a player, $t^i\in S^i$, $R^i\subseteq S^i$ a Borel set, and $\zeta^i$ the map with $\zeta^i(s^i)=t^i$ for $s^i\in R^i$ and $\zeta^i(s^i)=s^i$ otherwise. Then the integrand of (4) is integrable and
--   $$
--   \int_S\bigl[h^i(s)-h^i\bigl(s^{-i},\zeta^i(s^i)\bigr)\bigr]\,dp(s)\ \ge\ 0 .
--   $$
--
--   This is the first half of the proof that the cluster point $p$ is a correlated equilibrium; the general measurable deviation is reduced to finitely many deviations of this form.
--
--   **Formalization Note** The paper's sentence reads "$\zeta^i(s^i)=t^i$ for all $t^i\in R^i$", a misprint for "for all $s^i\in R^i$"; the corrected reading is encoded. The paper indexes the net by all f-sets ordered by inclusion, which is not a directed set (two f-sets differing on infinitely many singleton coordinates have no common upper bound); the net here runs over the f-sets containing the fixed profile $\hat s$, which are directed and still contain an f-set with $T^i\supseteq\{t^i\}$ above any given one, as the proof requires.
-- source:
--   Hart and Schmeidler, Existence of Correlated Equilibria, Math. Oper. Res. 14 (1989), pp. 24–25, proof of Theorem 3, "A special case" through "that (4) holds"; https://doi.org/10.1287/moor.14.1.18

import Definitions.Def_HartSchmeidler_Compact_Game

namespace HartSchmeidler.Compact

open MeasureTheory

/-- Proof of Theorem 3, pp. 24–25, the special case: let `p` be a regular probability measure
on `S` that is a cluster point, against continuous functions, of the correlated equilibria
`q_T` of the f-set games `Γ_T` (`T` ranging over the f-sets containing a fixed profile `ŝ`).
Then (4) holds for every deviation `ζⁱ` with `ζⁱ = tⁱ` on a Borel set `Rⁱ` and the identity
elsewhere. -/
theorem special_case {ι : Type*} [Nonempty ι] [DecidableEq ι] {S : ι → Type*}
    [∀ i, TopologicalSpace (S i)] [∀ i, CompactSpace (S i)] [∀ i, T2Space (S i)]
    [∀ i, Nonempty (S i)] [∀ i, MeasurableSpace (S i)] [∀ i, BorelSpace (S i)]
    (h : ι → Profile S → ℝ) (hcont : ∀ i, Continuous (h i))
    (ŝ : Profile S)
    (F : (∀ i, Finset (S i)) → Finset (Profile S)) (w : (∀ i, Finset (S i)) → Profile S → ℝ)
    (hFw : ∀ T, IsAnchoredFSet ŝ T → IsFSetCE h T (F T) (w T))
    (p : Measure (Profile S)) [IsProbabilityMeasure p] (hp : p.Regular)
    (hclus : ∀ (f : C(Profile S, ℝ)) (ε : ℝ), 0 < ε →
      ∀ T₀, IsAnchoredFSet ŝ T₀ → ∃ T, IsAnchoredFSet ŝ T ∧ (∀ i, T₀ i ⊆ T i) ∧
        |∫ s, f s ∂p - ∑ s ∈ F T, w T s * f s| < ε)
    (i : ι) (t : S i) (R : Set (S i)) (hR : MeasurableSet R) :
    Integrable
        (fun s : Profile S => h i s - h i (Function.update s i (specialDeviation t R (s i)))) p ∧
      0 ≤ ∫ s : Profile S, (h i s - h i (Function.update s i (specialDeviation t R (s i)))) ∂p := by sorry

end HartSchmeidler.Compact
