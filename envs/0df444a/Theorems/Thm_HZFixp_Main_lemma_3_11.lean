-- Prove2me | Theorems.Thm_HZFixp_Main_lemma_3_11
-- name    : HZFixp.Main.lemma_3_11
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T01:53:52.561123+00:00
-- url     : https://prove2.me/theorems/badc01be-5612-4e08-9d33-3972a6aadaeb
-- title:
--   Lemma 3.11 — the market lemma: supporting prices (15), box conditions, full spending, edge demand (16)
-- statement:
--   Let $(X,p)$ be an HZ equilibrium of the market of §3.4.1 built from a Reciprocal VI instance. Then there is $r$ with $r_i\in[a_i,b_i]$ such that $X$ is also supported by the prices
--   $$\pi_R=1,\qquad \pi^+_i=1+\frac1{r_i},\qquad \pi^-_{it}=1-\frac{\lambda_{it}}{r_i} \tag{15}$$
--   (that is, $(X,\pi)$ is an HZ equilibrium); $r$ satisfies the box conditions (3) of the graph; at $\pi$ every optimal bundle of every agent spends exactly one; and every optimal bundle $y$ of the edge agent of $e:i\to j$ puts weight only on its low group and its selected high goods, with
--   $$q^-_e=\frac{r_i}{r_i+\lambda_e r_j},\qquad q^+_e=\frac{\lambda_e r_j}{r_i+\lambda_e r_j} \tag{16}$$
--   the total quantities on the two.
--
--   With the designated-pair promise, this lets each designated coordinate be read off one allocation entry, which is the recovery map of Theorem 3.6.
--
--   Differences from the source:
--   - encoding: the market's N agents and N goods in construction order → typed agents MAgent and goods MGood (node agents by node and copy, edge agents by edge; low goods by group and copy, high goods by node and copy, reference goods); equilibria are CardinalMatching.IsApproxHZ at ε = 0 over these types; reason: a relabelling of rows and columns; the lemmas do not depend on the order
--   - reading: π⁻_it for the low groups at node i → 1 − λ/r_i for every low group, the auxiliary group (parameter a_i) included; reason: (15) indexes all low groups it of node i
-- source:
--   Liu, Tao, Yan, Settling the Complexity of Hylland–Zeckhauser Equilibria, arXiv:2606.06317 (held version later than v2, sha256 36e91522…af1c), p. 24–25 (PDF 26–27), Lemma 3.11, (15), (16); proof B.2.2, pp. 60–61 (PDF 62–63)

import Mathlib
import Definitions.Def_FixpReciprocal_RealSearch
import Definitions.Def_CardinalMatching_IsApproxHZ
import Definitions.Def_HZFixp_Main_ReciprocalVI
import Definitions.Def_HZFixp_Main_Market

open FixpReciprocal

namespace HZFixp.Main

/-- **Lemma 3.11.** Every equilibrium allocation of the market of §3.4.1 admits supporting prices
of the form (15), `π_R = 1`, `π⁺_i = 1 + 1/r_i`, `π⁻_{it} = 1 − λ_{it}/r_i`, `r_i ∈ [a_i, b_i]`;
`r` satisfies the box conditions (3); at these prices every optimal bundle exhausts the unit
budget; and every optimal bundle of the edge agent of `e : i → j` uses only its selected low and
high goods, in total quantities `q⁻_e = r_i/(r_i + λ_e r_j)` and `q⁺_e = λ_e r_j/(r_i + λ_e r_j)`
(16). -/
theorem lemma_3_11 (I : RVIInst) (X : MAgent I.1 → MGood I.1 → ℝ) (p : MGood I.1 → ℝ)
    (hX : CardinalMatching.IsApproxHZ I.1.mUtil 0 X p) :
    ∃ r : Fin I.1.k → ℝ,
      (∀ i, (I.1.lo i.val : ℝ) ≤ r i ∧ r i ≤ (I.1.hi i.val : ℝ)) ∧
      CardinalMatching.IsApproxHZ I.1.mUtil 0 X (I.1.price15 r) ∧
      I.1.IsBoxSol r ∧
      (∀ a y, IsOptBundle (I.1.mUtil a) (I.1.price15 r) y →
        ∑ g, I.1.price15 r g * y g = 1) ∧
      ∀ (e : Fin I.1.W) (y : MGood I.1 → ℝ),
        IsOptBundle (I.1.mUtil (edgeAgent e)) (I.1.price15 r) y →
        (∀ g, y g ≠ 0 → I.1.IsEdgeLow e g ∨ I.1.IsEdgeHigh e g) ∧
        massOn (I.1.IsEdgeLow e) y = lookup r (I.1.edgeAt e).1 /
          (lookup r (I.1.edgeAt e).1 + ((I.1.edgeAt e).2.2 : ℝ) * lookup r (I.1.edgeAt e).2.1) ∧
        massOn (I.1.IsEdgeHigh e) y = ((I.1.edgeAt e).2.2 : ℝ) * lookup r (I.1.edgeAt e).2.1 /
          (lookup r (I.1.edgeAt e).1 +
            ((I.1.edgeAt e).2.2 : ℝ) * lookup r (I.1.edgeAt e).2.1) := by sorry

end HZFixp.Main
