-- Prove2me | Theorems.Thm_ModularCurve_exists_algHom_of_isRoot
-- name    : ModularCurve.exists_algHom_of_isRoot
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.209688+00:00
-- url     : https://prove2.me/theorems/7a37c831-c213-5e25-982f-863e3a0bc5a2
-- title:
--   Prescribing a root of Φ_N by an L-algebra map
-- statement:
--   Let $L$ be a field equipped with a $\mathbb{Q}$-algebra structure, let $N$ be a nonzero natural number, and let `data` be a `ModularPolynomialData N`, that is, a polynomial $\Phi \in (\mathbb{Z}[X])[Y]$ which is monic, has degree $\psi(N) = \sum_{d \mid N,\ d \text{ squarefree}} N/d$, and satisfies $\Phi = 0$ after substituting the Laurent series $jq = q^{-1}\cdot jNumQ \in \mathbb{Q}((q))$ for the inner variable $X$ and $\mathrm{qExpand}\ \mathbb{Q}\ N\ jq$ (the effect of $q \mapsto q^N$ on $jq$) for $Y$. Let $A$ be a field extension of $L$ and let $c, y \in A$ be such that $c$ is transcendental over $L$ and $y$ is a root of the one-variable polynomial over $A$ obtained from $\Phi$ by mapping each coefficient in $\mathbb{Z}[X]$ to its value at $c$ under the integer-coefficient map into $A$. Then there is an $L$-algebra homomorphism $\psi$ from `laurentBaseChange L (modularFunctionFieldFull N)` — the subfield of $L((q))$ generated over $L$ by the coefficientwise images under $\mathbb{Q} \to L$ of the elements of the subfield of $\mathbb{Q}((q))$ generated over $\mathbb{Q}$ by the expansions $\mathrm{qExpand}\ \mathbb{Q}\ d\ jq$ for the nonzero divisors $d$ of $N$ — into $A$, carrying the image of $jq$ to $c$ and the image of $\mathrm{qExpand}\ \mathbb{Q}\ N\ jq$ to $y$.
--
--   This is the existence half of the description of $A$-valued points of the formal model of $X_0(N)$: once the $j$-coordinate is specified by a transcendental element $c$ of $A$, every root in $A$ of $\Phi_N(c, Y)$ is realised as the image of $j(q^N)$ under some $L$-algebra map out of the base-changed level-$N$ modular function field. It is used in [`ModularCurve.exists_emb_equiv_rootsAt`](thm.html#ModularCurve.exists_emb_equiv_rootsAt), which turns this into a bijection between such embeddings and the root set.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_algHom_of_isRoot.lean

import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_QAdicPlace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve

theorem ModularCurve.exists_algHom_of_isRoot (L : Type*) [Field L] [Algebra ℚ L] (N : ℕ) [NeZero N]
    (data : ModularPolynomialData N) {A : Type*} [Field A] [Algebra L A] (c y : A)
    (hc : Transcendental L c)
    (hy : (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom A) c)).IsRoot y) :
    ∃ ψ : laurentBaseChange L (modularFunctionFieldFull N) →ₐ[L] A,
      ψ ⟨coeffEmb L jq, coeffEmb_mem_laurentBaseChange L (jq_mem_full N)⟩ = c ∧
      ψ ⟨coeffEmb L (qExpand ℚ N jq),
        coeffEmb_mem_laurentBaseChange L (jqd_mem_full N (dvd_refl N))⟩ = y := by sorry
