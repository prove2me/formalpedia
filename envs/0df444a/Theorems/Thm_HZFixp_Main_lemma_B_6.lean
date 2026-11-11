-- Prove2me | Theorems.Thm_HZFixp_Main_lemma_B_6
-- name    : HZFixp.Main.lemma_B_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T01:54:07.461802+00:00
-- url     : https://prove2.me/theorems/124fd5e7-8d8a-46ff-bf1a-00b90e1ec76b
-- title:
--   Lemma B.6 — high and reference consumption and the price relations at the normalized prices
-- statement:
--   Let $(X,p)$ be an HZ equilibrium of the market of §3.4.1 built from a Reciprocal VI instance, let $\hat p = (p-m)/(1-m)$ with $m=\min_g p_g$ be the normalized prices, and for a node $i$ let $(\gamma_i,\mu_i)$ be any optimum of the demand dual (50) of the node-$i$ agents at $\hat p$, with $r_i=(b_i+1)\gamma_i$. Then the node-$i$ agents together consume a positive amount of the ordinary (non-reserved) high goods at $i$ and of the reference goods; every reserved high good at $i$ has the price of the ordinary high goods at $i$; and
--   $$\pi^+_i=\pi_R+\frac1{r_i},\qquad \pi^-_{it}\ge\pi_R-\frac{\lambda_{it}}{r_i},\qquad \pi_R\le1,$$
--   for the normalized price $\pi^+_i$ of any ordinary high good at $i$, $\pi^-_{it}$ of any low good of group $t$ at $i$, and $\pi_R$ of any reference good.
--
--   These relations, made tight by Lemma B.7, give the prices (15) of Lemma 3.11.
--
--   Differences from the source:
--   - encoding: the market's N agents and N goods in construction order → typed agents MAgent and goods MGood (node agents by node and copy, edge agents by edge; low goods by group and copy, high goods by node and copy, reference goods); equilibria are CardinalMatching.IsApproxHZ at ε = 0 over these types; reason: a relabelling of rows and columns; the lemmas do not depend on the order
--   - reading: the normalized prices from Lemma B.5 and one chosen optimal dual pair (γ_i, µ_i) for node class i → normPrice p = (p − m)/(1 − m) of the given equilibrium prices, and every optimal dual pair of the node-i utility row; reason: these are the prices the proof of B.5 constructs; the lemma holds for any choice of the dual pair
-- source:
--   Liu, Tao, Yan, Settling the Complexity of Hylland–Zeckhauser Equilibria, arXiv:2606.06317 (held version later than v2, sha256 36e91522…af1c), p. 58 (PDF 60), Lemma B.6

import Mathlib
import Definitions.Def_CardinalMatching_IsApproxHZ
import Definitions.Def_HZFixp_Main_ReciprocalVI
import Definitions.Def_HZFixp_Main_Market

namespace HZFixp.Main

/-- **Lemma B.6.** At the normalized prices `π̂ = (π − m)/(1 − m)` of an equilibrium of the market
of §3.4.1, with `r_i = (b_i + 1)γ_i` for an optimal demand dual `(γ_i, µ_i)` of node class `i`:
every node class consumes positive amounts of its ordinary high goods and the reference goods;
every reserved high good has the same price as its node's ordinary high goods; and
`π⁺_i = π_R + 1/r_i`, `π⁻_{it} ≥ π_R − λ_{it}/r_i`, `π_R ≤ 1`. -/
theorem lemma_B_6 (I : RVIInst) (X : MAgent I.1 → MGood I.1 → ℝ) (p : MGood I.1 → ℝ)
    (hX : CardinalMatching.IsApproxHZ I.1.mUtil 0 X p) (i : Fin I.1.k) (γ μ : ℝ)
    (hd : IsOptDemandDual (I.1.nodeUtil i) (normPrice p) γ μ) :
    0 < I.1.classCons X i (fun g => I.1.IsHighAt i g ∧ ¬ I.1.IsReserved g) ∧
    0 < I.1.classCons X i I.1.IsRef ∧
    (∀ g g', I.1.IsHighAt i g → I.1.IsReserved g → I.1.IsHighAt i g' → ¬ I.1.IsReserved g' →
      normPrice p g = normPrice p g') ∧
    (∀ g g', I.1.IsHighAt i g → ¬ I.1.IsReserved g → I.1.IsRef g' →
      normPrice p g = normPrice p g' + 1 / (((I.1.hi i : ℝ) + 1) * γ)) ∧
    (∀ g g', I.1.IsLowAt i g → I.1.IsRef g' →
      normPrice p g' - (I.1.goodParam g : ℝ) / (((I.1.hi i : ℝ) + 1) * γ) ≤ normPrice p g) ∧
    (∀ g', I.1.IsRef g' → normPrice p g' ≤ 1) := by sorry

end HZFixp.Main
