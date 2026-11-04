-- Prove2me | Theorems.Thm_OAI_SignedSweeps_occupied_block_type_angle_exp_all
-- name    : OAI.SignedSweeps.occupied_block_type_angle_exp_all
-- status  : Proved
-- author  : @wurtle
-- created : 2026-11-03T23:35:42.935623+00:00
-- url     : https://prove2.me/theorems/2302a7f8-6abe-41bb-a378-d0b1150d7939
-- title:
--   Angle between column types, row types and a global signed type on a punctured rectangle
-- statement:
--   This is the angle estimate between prescribed column types, prescribed row types and a prescribed global signed type on a rectangle with marked cells removed.
--
--   Throughout, $S_p$ acts on the word space $W_p=\ell^2\big((C\sqcup C)^p\big)$, with $C=\{1,\dots,q\}$ two-coloured into even and odd letters, by the signed action $(\rho(g)f)(w)=\varepsilon(g,w)\,f(w\circ g)$, where $\varepsilon(g,w)$ is the sign of the permutation $g$ induces between the odd positions of $w$. For $u+v=p$ and partitions $\alpha\vdash u$, $\beta\vdash v$, the operator $P_{\alpha,\beta}$ is the sum, over the placements of $u$ even sites among the $p$ sites, of the tensor product of the orthogonal projections onto the $S^\alpha$-isotypic part of the $u$ even sites and the $S^\beta$-isotypic part of the $v$ odd sites. Its entropy is $F(\alpha,\beta)=\sum_{a\in\alpha\cup\beta}a\log\frac{u+v}{a}$, and a *local type* on $k$ sites is such a pair of total size $k$. For an enumeration $e$ of the $p$ sites by blocks $j\in J$ with $k_j$ sites each and local types $t=(t_j)_j$, $P^{e}_{t}$ is the corresponding tensor product of local type projections, with $F(t)=\sum_jF(t_j)$. For a coefficient function $f:G\to\mathbb{C}$ on a finite group and a representation $\pi$, $\pi(f)=\sum_gf(g)\pi(g)$.
--
--   Let $A,B$ be finite with $B$ nonempty, let $e:\{1,\dots,n\}\to A\times B$ be a bijection, and let $p+l=n$. Fix an injection $z$ of $l$ marks into the $n$ positions, and let $x\mapsto\iota(x)$ enumerate the remaining $p$ positions. Let $e_H$ enumerate these $p$ sites by column, with $k^H_j\le s$ sites in column $j\in B$, and let $e_K$ enumerate them by row, with $k^K_i\le m$ sites in row $i\in A$, compatibly with $e$ and $\iota$. Let $H=(H_j)$ and $K=(K_i)$ be local types on these blocks. Let $u+v=p$ with $\alpha\vdash u$, $\beta\vdash v$ having at most $q\ge1$ rows, and let $R\ge\max(s,m)+1$. Then
--
--   $$
--   \big\|P^{e_H}_{H}\,P^{e_K}_{K}\,P_{\alpha,\beta}\big\|^2\le\min\Big\{1,\ \exp\Big(F(H)+F(K)-F(\alpha,\beta)+l+(|A|+|B|)\,2q^2\log R\Big)\Big\}.
--   $$
--
--   The estimate converts the entropies of line types into the global entropy; the removed cells cost only the factor $e^l$, with no assumption on their arrangement.
--
--   **Formalization Note** The norm is the operator norm on $W_p$. The upstream statement is reproduced verbatim from `BlockAngle.lean`.
-- source:
--   OpenAI, "Signed tensor densities and diagram budgets for the Thorp shuffle" (September 26, 2026), openai/math preprints/Signed-tensor-densities-and-diagram-budgets-for-coordinate-sweeps-September-26-2026/paper.pdf, Section 3, Theorem 3.2, and Section 4.6, eq. (25). Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SignedSweeps/BlockAngle.lean#L54-L84

import Mathlib
import Definitions.Def_SignedSweepMoment
import Definitions.Def_OAISignedSweepsProofDefs

open scoped BigOperators Classical

theorem OAI.SignedSweeps.occupied_block_type_angle_exp_all {A B : Type} [Fintype A] [Fintype B] [Nonempty B]
    {q p l n s m R : ℕ} (hq : 0 < q)
    (hn : p+l=n) (e : Fin n ≃ A × B) (z : MarkedAssignment l n)
    {kH : B → ℕ} {kK : A → ℕ}
    (eH : (Σ j, Fin (kH j)) ≃ Fin p)
    (hHroute : ∀ x, (eH.symm x).1 = (e (markedInjection hn z x)).2)
    (eK : (Σ i, Fin (kK i)) ≃ Fin p)
    (hKroute : ∀ x, (eK.symm x).1 = (e (markedInjection hn z x)).1)
    (H : ∀ j, PairType (kH j)) (K : ∀ i, PairType (kK i))
    (hkH : ∀ j, kH j ≤ s) (hkK : ∀ i, kK i ≤ m)
    (hR : max s m+1 ≤ R)
    {u v : ℕ} (h : u+v=p) (a : Partition u) (b : Partition v)
    (ha : a.1.colLen 0 ≤ q) (hb : b.1.colLen 0 ≤ q) :
    ‖(blockTypeProjection (C:=Fin q) eH H * blockTypeProjection eK K *
      pairTypeProjection h a b (Fin q)).toContinuousLinearMap‖^2 ≤
      min 1 (Real.exp (blockEntropy H+blockEntropy K-signedEntropy a b+l+
        ((Fintype.card A : ℝ)+Fintype.card B)*(2*(q:ℝ)^2*Real.log R))) := by sorry
