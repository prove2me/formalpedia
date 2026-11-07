-- Prove2me | Theorems.Thm_MatMulDS_proposition_7_1
-- name    : MatMulDS.proposition_7_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:07:04.280451+00:00
-- url     : https://prove2.me/theorems/16415f41-51d7-41ac-9fc7-1d96080649f7
-- title:
--   Proposition 7.1 — rates of the identity with $5^4$ products
-- statement:
--   Let $p$ be a distribution on the types $\tau\subseteq[4]$ with rational values, and let $\pi$ give every output of $T_5^{(4)}$ of type $\tau$ the probability $p_\tau/4^{4-|\tau|}$. Let $\mathsf w$ be a nonnegative monotone function on the subsets of $[4]$, and give every product $R$ the weight $\mathsf w(S(R))$. Then $\pi$ has rational values and is uniform within each block, the weight function is compatible with the private map of §7.1, and it is strict if $\mathsf w(S)=|S|$. For every threshold $\eta_{\mathrm{pre}}$ and every $\theta\ge0$,
--   $$H(\pi)=H(p)+\sum_\tau p_\tau(4-|\tau|)\log4,\quad\mathrm{len}(\pi)=\sum_\tau p_\tau\log d_\tau,\quad\log P_{\mathrm{base}}=4\log5,\quad\mu=\sum_\tau p_\tau\mathsf w(\tau),$$
--   $$f=\log\sum_{S\subseteq[4]}4^{4-|S|}e^{-\theta\mathsf w(S)}+\theta\eta_{\mathrm{pre}},\quad\xi=\sum_\tau p_\tau\log\sum_{S\subseteq\tau}4^{|\tau|-|S|}e^{-(\mathsf w(\tau)-\mathsf w(S))}+\mu-\eta_{\mathrm{pre}}.$$
--
--   These formulas turn the data structure's costs into a finite computation.
--
--   Differences from the source:
--   - reading: $T_5^{(4)}$, "the identity with $5^4$ products" → any identity obtained by the construction (`IsTFour`); reason: the construction makes choices, and the claim holds for each of them
--   - encoding: positions in $[4]$, 1-based → $\mathrm{Fin}\,4$; reason: same instances
-- source:
--   J. Alman, J. Nogler, V. Vassilevska Williams, Subquadratic Time Matrix Multiplication Data Structures Beyond the Dual Exponent, with Applications, STOC 2027 submission (held file sha256 6c5a1c16…), Proposition 7.1, eq. (7.2), p.45 (PDF p.47)

import Mathlib
import Definitions.Def_MatMulDS_outPos

set_option autoImplicit false

namespace MatMulDS

/-- **Proposition 7.1 (Rates of the Identity with 5⁴ Products), p.45** (Alman, Nogler, Vassilevska Williams, STOC 2027
submission, held file sha256 6c5a1c16…). Let `p` be a distribution on the types `τ ⊆ [4]` with rational values, and let
`π` give every output of type `τ` the probability `p_τ / 4^{4−|τ|}`. Let `w` be a nonnegative monotone function on the
subsets of `[4]`, and give every product `R` the weight `w(S(R))`. Then `π` has rational values and is uniform within each
block, the weight function is compatible with the private map of §7.1, and it is strict if `w(S) = |S|`. For every threshold
`η_pre` and every `θ ≥ 0`, the quantities of (5.4), (5.5) are given by (7.2).

**Formalization Note** `T5^(4)` is any identity obtained by the construction (`IsTFour`): the construction makes
choices, and the claim holds for each of them, because enlargement keeps the outputs, blocks and relevant products. The
private map `privFour` is the one written out on p.44. -/
theorem proposition_7_1 {n₁ n₂ : ℕ}
    (T₁ : BlockTensor (Fin 3 × Fin 3) ((Fin 2 × Fin 2) ⊕ Fin n₁) (Fin 2 × Fin 2) (Fin 2 × Fin 2))
    (D₁ : IdentityData (Fin 3 × Fin 3) ((Fin 2 × Fin 2) ⊕ Fin n₁) (Fin 2 × Fin 2) (Fin 5 × Fin 5))
    (T₂ : BlockTensor ((Fin 3 × Fin 3) × (Fin 3 × Fin 3))
      ((((Fin 2 × Fin 2) ⊕ Fin n₁) × ((Fin 2 × Fin 2) ⊕ Fin n₁)) ⊕ Fin n₂)
      ((Fin 2 × Fin 2) × (Fin 2 × Fin 2)) ((Fin 2 × Fin 2) × (Fin 2 × Fin 2)))
    (D₂ : IdentityData ((Fin 3 × Fin 3) × (Fin 3 × Fin 3))
      ((((Fin 2 × Fin 2) ⊕ Fin n₁) × ((Fin 2 × Fin 2) ⊕ Fin n₁)) ⊕ Fin n₂)
      ((Fin 2 × Fin 2) × (Fin 2 × Fin 2)) P4)
    (hT : IsTFour T₁ D₁ T₂ D₂)
    (p : Finset (Fin 4) → ℚ) (hp0 : ∀ τ, 0 ≤ p τ) (hp1 : ∑ τ, p τ = 1)
    (w : Finset (Fin 4) → ℝ) (hw0 : ∀ S, 0 ≤ w S) (hwm : ∀ S τ, S ⊆ τ → w S ≤ w τ) :
    let π := piFour p
    let wt : P4 → ℝ := fun R => w (defaultSet R)
    let ρ : T₂.Out → P4 := fun o => privFour o.1
    IsBlockDistribution T₂ π ∧
    D₂.IsPrivateMap T₂ ρ ∧
    D₂.IsCompatible T₂ ρ wt ∧
    ((∀ S, w S = (S.card : ℝ)) → D₂.IsStrict T₂ ρ wt) ∧
    ∀ η θ : ℝ, 0 ≤ θ →
      entropy T₂ π = (∑ τ, Real.negMulLog (p τ : ℝ)) +
        ∑ τ : Finset (Fin 4), (p τ : ℝ) * ((4 - (τ.card : ℝ)) * Real.log 4) ∧
      lenPi T₂ π = ∑ τ, (p τ : ℝ) * Real.log (lenOfType τ) ∧
      logP P4 = 4 * Real.log 5 ∧
      mu π ρ wt = ∑ τ, (p τ : ℝ) * w τ ∧
      fRate wt θ η =
        Real.log (∑ S : Finset (Fin 4), (4 : ℝ) ^ (4 - S.card) * Real.exp (-θ * w S)) + θ * η ∧
      xiRate D₂ π ρ wt η =
        (∑ τ : Finset (Fin 4), (p τ : ℝ) *
          Real.log (∑ S ∈ τ.powerset, (4 : ℝ) ^ (τ.card - S.card) * Real.exp (-(w τ - w S)))) +
        (∑ τ, (p τ : ℝ) * w τ) - η := by sorry

end MatMulDS
