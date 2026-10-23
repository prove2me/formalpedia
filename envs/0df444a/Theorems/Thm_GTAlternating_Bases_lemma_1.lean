-- Prove2me | Theorems.Thm_GTAlternating_Bases_lemma_1
-- name    : GTAlternating.Bases.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:28:13.148077+00:00
-- url     : https://prove2.me/theorems/9d58cbfe-62f2-45e2-af0c-ef8a53ba9e83
-- title:
--   Lemma 1, p. 4 — a vector lies in V_γ iff it is in the V_{α^{(n−1)}}-isotypic subspace and is the image of a GT vector of the previous level
-- statement:
--   Let $\underline\alpha = (\alpha^{(2)},\dots,\alpha^{(n)}) \in \tilde{\mathcal S}(\alpha)$ with $\alpha^{(n)} = \alpha$ and $\beta = \alpha^{(n-1)}$, and write $V_{(\beta,\alpha)}$ for the $A_{n-1}$-isotypic subspace of $V_\alpha$ of type $V_\beta$. A vector $x \in V_{\mathrm{shape}(\alpha)}$ lies in the Gelfand–Tsetlin subspace $V_{\underline\alpha}$ if and only if
--
--   1. $x$ lies in $V_\alpha$ and in the $A_{n-1}$-isotypic subspace of type $V_\beta$, and
--   2. there is an $A_{n-1}$-equivariant linear map $\phi$ that restricts to an isomorphism $V_\beta \xrightarrow{\ \sim\ } V_{(\beta,\alpha)}$, and a vector $y$ in the Gelfand–Tsetlin subspace $V_{(\alpha^{(2)},\dots,\alpha^{(n-1)})}$ of $V_\beta$, with
--   $$x = \phi(y).$$
--
--   This is the recursive characterisation of Gelfand–Tsetlin subspaces used in the proof of the Main Theorem: one checks that $u_{\underline\alpha}$ lies in the right isotypic subspace and is the image of the previous level's vector.
--
--   **Formalization Note.** The paper states Lemma 1 for an arbitrary tower of groups with multiplicity-free restrictions; here it is posed for the tower of alternating groups in Young's model, and for a path in $\tilde{\mathcal S}(\alpha)$ (the paper's $T \in \mathcal T(\lambda)$). "Under an isomorphism $\phi$" is read existentially; by Schur's lemma any two such isomorphisms differ by a scalar. $A_k$-equivariance is commutation with the products $\rho(s_i)\rho(s_j)$, $i,j \le k-1$, which generate $A_k$ (Young's formulas define a representation by [5, Theorem 2.1]). Labels are 0-based; paths are stored top-down.
-- source:
--   Geetha, Prasad, Comparison of Gelfand-Tsetlin bases for alternating and symmetric groups, arXiv:1606.04424v2, p. 4, Lemma 1 (specialised to the alternating tower)

import Mathlib
import Definitions.Def_GTAlternating_Bases_Model

namespace GTAlternating.Bases

theorem lemma_1 (a b : Label) (rest : List Label) (hp : IsPath a (b :: rest)) (x : V a.shape) :
    x ∈ GTLine a (b :: rest) ↔
      (x ∈ a.space ∧ x ∈ Iso b.size b.space a.shape ∧
        ∃ f : V b.shape →ₗ[ℂ] V a.shape, IsAltEquivariant b.size f ∧ Set.InjOn f b.space ∧
          b.space.map f = Iso b.size b.space a.shape ⊓ a.space ∧
          ∃ y ∈ GTLine b rest, f y = x) := by sorry

end GTAlternating.Bases
