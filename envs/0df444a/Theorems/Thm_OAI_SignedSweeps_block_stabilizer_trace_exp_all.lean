-- Prove2me | Theorems.Thm_OAI_SignedSweeps_block_stabilizer_trace_exp_all
-- name    : OAI.SignedSweeps.block_stabilizer_trace_exp_all
-- status  : Proved
-- author  : @wurtle
-- created : 2026-11-03T23:35:29.158743+00:00
-- url     : https://prove2.me/theorems/99446dff-c6e2-4e29-9db6-ff129ae3d7ab
-- title:
--   Product of local stabilizer traces for prescribed block types
-- statement:
--   This is the local stabilizer trace estimate of the signed sweep moment induction, in product form over the blocks of a rectangle.
--
--   Throughout, $S_p$ acts on the word space $W_p=\ell^2\big((C\sqcup C)^p\big)$, with $C=\{1,\dots,q\}$ two-coloured into even and odd letters, by the signed action $(\rho(g)f)(w)=\varepsilon(g,w)\,f(w\circ g)$, where $\varepsilon(g,w)$ is the sign of the permutation $g$ induces between the odd positions of $w$. For $u+v=p$ and partitions $\alpha\vdash u$, $\beta\vdash v$, the operator $P_{\alpha,\beta}$ is the sum, over the placements of $u$ even sites among the $p$ sites, of the tensor product of the orthogonal projections onto the $S^\alpha$-isotypic part of the $u$ even sites and the $S^\beta$-isotypic part of the $v$ odd sites. Its entropy is $F(\alpha,\beta)=\sum_{a\in\alpha\cup\beta}a\log\frac{u+v}{a}$, and a *local type* on $k$ sites is such a pair of total size $k$. For an enumeration $e$ of the $p$ sites by blocks $j\in J$ with $k_j$ sites each and local types $t=(t_j)_j$, $P^{e}_{t}$ is the corresponding tensor product of local type projections, with $F(t)=\sum_jF(t_j)$. For a coefficient function $f:G\to\mathbb{C}$ on a finite group and a representation $\pi$, $\pi(f)=\sum_gf(g)\pi(g)$.
--
--   Let $J$ be a finite index set, let $k_j\le t$ for $j\in J$, let $e$ enumerate $p=\sum_jk_j$ sites by the blocks, and fix local types $a_j$ on $k_j$ sites and injections $i_j:\{1,\dots,k_j\}\hookrightarrow\{1,\dots,t\}$. Let $f_j:S_t\to\mathbb{C}$ act as a positive operator in the regular representation, let $\eta,G_j\in\mathbb{R}$, and let $R\ge 2t+2q+1$. Assume that for every $j$ with $a_j$ of height at most $q$, for all $\lambda\vdash t$ and all partitions $c$ of $t-k_j$ such that $\lambda$ contains the signed occurrence of $(a_j,c)$,
--
--   $$
--   \dim S^\lambda\cdot\operatorname{Re}\operatorname{Tr}_{S^\lambda}\pi_\lambda(f_j)\le\exp\big(\eta F(a_j)+G_j\big).
--   $$
--
--   Write $\tilde f$ for the coefficient on $S_p$ obtained by pushing the product of the restrictions $g\mapsto f_j(g^{i_j})$ along the block embedding $\prod_jS_{k_j}\to S_p$, where $g^{i_j}$ acts as $g$ on the image of $i_j$ and fixes the other points. Then
--
--   $$
--   \operatorname{Re}\operatorname{Tr}_{W_p}\big(P^e_a\,\rho(\tilde f)\big)\le\prod_{j}\frac{k_j!}{t!}\cdot\exp\Big((\eta-1)F(a)+\sum_jG_j+|J|\,E_{\mathrm{loc}}(t,q,R)\Big),
--   $$
--
--   where $E_{\mathrm{loc}}(t,q,R)=\big(2\lfloor\sqrt t\rfloor+26q^2+8q+1\big)\log R+8q+1$.
--
--   This reduces traces on the occupied part of a rectangle to the inductive moment bound on each line, with the exact pointwise-stabilizer index retained.
--
--   **Formalization Note** The hypothesis is stated only for types of height at most $q$, and the bound also covers types of larger height. The upstream statement is reproduced verbatim from `OccupiedTrace.lean`.
-- source:
--   OpenAI, "Signed tensor densities and diagram budgets for the Thorp shuffle" (September 26, 2026), openai/math preprints/Signed-tensor-densities-and-diagram-budgets-for-coordinate-sweeps-September-26-2026/paper.pdf, Section 3, Lemma 3.5, eq. (16), and Section 4.5, eqs. (22)-(23). Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SignedSweeps/OccupiedTrace.lean#L9-L36

import Mathlib
import Definitions.Def_SignedSweepMoment
import Definitions.Def_OAISignedSweepsProofDefs

open scoped BigOperators Classical

theorem OAI.SignedSweeps.block_stabilizer_trace_exp_all {J : Type*} [Fintype J]
    {p t q R : ℕ} {k : J → ℕ}
    (e : (Σ j, Fin (k j)) ≃ Fin p) (a : ∀ j, PairType (k j))
    (hk : ∀ j, k j ≤ t) (i : ∀ j, Fin (k j) ↪ Fin t)
    (f : J → SymmetricGroup t → ℂ)
    (hf : ∀ j, (coefficientAction finiteRegularRepresentation (f j)).IsPositive)
    (η : ℝ) (G : J → ℝ)
    (hamb : ∀ j, (a j).height ≤ q → ∀ (lam : Partition t) (c : Partition (t-k j)),
      SignedOccurrence ((a j).extended_size_eq (hk j)) (a j).2.1 (a j).2.2 c lam →
      (spechtDimension lam : ℝ) *
        (LinearMap.trace ℂ (Specht lam) (coefficientAction (spechtRepresentation lam) (f j))).re ≤
          Real.exp (η*(a j).entropy+G j))
    (hR : 2*t+2*q+1 ≤ R) :
    (LinearMap.trace ℂ (WordSpace p (Fin q ⊕ Fin q))
      (blockTypeProjection e a * coefficientAction (signedWordRepresentation p (Fin q))
        (coefficientPush (blockPermutation e)
          (productCoefficient (fun j g => f j (g.viaEmbedding (i j))))))).re ≤
      (∏ j, ((k j).factorial : ℝ)/t.factorial) *
        Real.exp ((η-1)*blockEntropy a+(∑ j, G j)+
          (Fintype.card J : ℝ)*localTraceError t q R) := by sorry
