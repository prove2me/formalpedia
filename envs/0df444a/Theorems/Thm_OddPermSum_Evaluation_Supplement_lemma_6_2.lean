-- Prove2me | Theorems.Thm_OddPermSum_Evaluation_Supplement_lemma_6_2
-- name    : OddPermSum.Evaluation.Supplement.lemma_6_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:43:39.554131+00:00
-- url     : https://prove2.me/theorems/5588680f-6dca-4f3e-8c30-5aa44839e06f
-- title:
--   Lemma 6.2 (used in the proof of Theorem 1.3) — Fixed Boolean border identities and units
-- statement:
--   Let $R_r=F[z]/(z^{r+1})$ with $F$ a characteristic-two field. Fix any vertex $u$ and set $M_b(X)=\left(\begin{smallmatrix}X&e_u\\e_u^\top&b\end{smallmatrix}\right)$ for $b=0,1$, placing the added index last. For every $X\in R_r^{n\times n}$,
--   $$\Phi(X)=\Phi(M_0(X))+\Phi(M_1(X)),\qquad G(X)_{j,i}=G(M_0(X))_{j,i}+G(M_1(X))_{j,i}\quad( i,j\in[n]).$$
--   If $X(0)=I-e_ue_u^\top$, both $M_0(X)$ and $M_1(X)$ have unit determinant in $R_r$.
--
--   The identities hold without an invertibility assumption on $X$. The final conditional clause permits valid inverse maintenance on both borders.
--
--   Differences from the source:
--   - encoding: original indices [n] and the new last border index → Fin n, Fin.castAdd into Fin (n+1), with the published border; reason: preserves the original matrix order and transposed derivative convention
--   - generalization: the finite field and n >= 2 working setting of sections 5–6 → every characteristic-two field and every n with a chosen vertex u : Fin n; reason: the formal border identities and constant-determinant argument on p. 20 are field-independent and also apply at n = 1
-- source:
--   Boxuan Chen, Bin Cui, Hanqing Li, Xupeng Miao, Haoze Wang, STOC 2027 submission #716 (October 2026), p. 19, Lemma 6.2

import Definitions.Def_OddPermSum_Evaluation_Supplement_truncatedRing
import Definitions.Def_OddPermSum_Evaluation_Supplement_rowUpdate
import Definitions.Def_OddPermSum_Evaluation_gradient

set_option autoImplicit false

namespace OddPermSum.Evaluation.Supplement

theorem lemma_6_2 {F : Type*} [Field F] [CharP F 2] {n r : ℕ}
    (u : Fin n) (X : Matrix (Fin n) (Fin n) (Trunc F r)) :
    phi X = phi (fixedBorder u X 0) + phi (fixedBorder u X 1) ∧
    (∀ i j : Fin n, gradient X j i =
      gradient (fixedBorder u X 0) (Fin.castAdd 1 j) (Fin.castAdd 1 i) +
      gradient (fixedBorder u X 1) (Fin.castAdd 1 j) (Fin.castAdd 1 i)) ∧
    ((constantMatrix X = fun i j => (if i = j then 1 else 0) -
        (if i = u ∧ j = u then 1 else 0)) →
      IsUnit (fixedBorder u X 0).det ∧ IsUnit (fixedBorder u X 1).det) := by sorry

end OddPermSum.Evaluation.Supplement
