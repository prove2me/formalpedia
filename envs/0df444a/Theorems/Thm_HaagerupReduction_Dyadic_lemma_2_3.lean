-- Prove2me | Theorems.Thm_HaagerupReduction_Dyadic_lemma_2_3
-- name    : HaagerupReduction.Dyadic.lemma_2_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:28:08.757907+00:00
-- url     : https://prove2.me/theorems/374a5165-4e43-4cd2-9e90-07cd8db3b03b
-- title:
--   Lemma 2.3, p. 7 — λ(t) ∈ Z(R_φ̂), and b_n is the unique element of Z(R_φ̂) with 0 ≤ b_n ≤ 2π and e^{ib_n} = λ(2^{-n})
-- statement:
--   Let $\mathcal R = M\rtimes_{\sigma^\varphi}G$, $\hat\varphi$, $\lambda$ and $b_n$ be as in the model, let $\mathcal R_{\hat\varphi} = \{x\in\mathcal R : \hat\varphi(xy) = \hat\varphi(yx)\ \forall y\in\mathcal R\}$ be the centralizer of $\hat\varphi$, and $Z(\mathcal R_{\hat\varphi})$ its center. Then:
--
--   1. $\lambda(t)\in Z(\mathcal R_{\hat\varphi})$ for every $t\in G$;
--   2. for every $n\in\mathbb N$, $b_n \in Z(\mathcal R_{\hat\varphi})$, $0\le b_n\le 2\pi$ and $e^{ib_n} = \lambda(2^{-n})$, and $b_n$ is the only element $b$ of $Z(\mathcal R_{\hat\varphi})$ with
--   $$0\le b\le 2\pi, \qquad e^{ib} = \lambda(2^{-n}).$$
--
--   Here $b_n = -i\,\mathrm{Log}\,\lambda(2^{-n})$ for the branch $0\le\operatorname{Im}\mathrm{Log}<2\pi$. The elements $b_n$, and $a_n = 2^nb_n$, are the logarithms from which the functionals $\varphi_n$ of (2.3) are built.
--
--   **Formalization Note.** $0 \le b\le 2\pi$ is the Loewner order on bounded operators ($b$ and $2\pi - b$ positive, hence self-adjoint). The centralizer is the commutation form valid for the bounded functional $\hat\varphi$ (p. 7), so no modular data are needed here. The paper writes "$0\le b_n\le2\pi$" although the branch gives $b_n<2\pi$ spectrally; the closed bound as printed is kept. $b_n$ is the Laurent operator defined in the model; part 2 certifies that it is the paper's $b_n$.
-- source:
--   Haagerup, Junge & Xu, A reduction method for noncommutative Lp-spaces and applications, arXiv:0806.3635v2, p. 7, Lemma 2.3 (definition of b_n in its proof)

import Mathlib
import Definitions.Def_BoundedRecovery
import Definitions.Def_HaagerupReduction_Dyadic_Model

namespace HaagerupReduction.Dyadic

universe u

open OAI.BoundedRecovery
open Filter Topology

/-- Lemma 2.3: `λ(t) ∈ Z(R_φ̂)`, and `b_n` is the unique element of `Z(R_φ̂)` with
`0 ≤ b_n ≤ 2π` and `e^{i b_n} = λ(2^{-n})`. -/
theorem lemma_2_3 {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (S : StandardModularData H) :
    (∀ t : dyadic, lam H t ∈
        centerOf (centralizerOf (crossedProduct S : Set (L2G H →L[ℂ] L2G H)) (phiHat S))) ∧
    ∀ n : ℕ,
      bOp H n ∈ centerOf (centralizerOf (crossedProduct S : Set (L2G H →L[ℂ] L2G H)) (phiHat S)) ∧
      0 ≤ bOp H n ∧ bOp H n ≤ ((2 * Real.pi : ℝ) : ℂ) • (1 : L2G H →L[ℂ] L2G H) ∧
      NormedSpace.exp (Complex.I • bOp H n) = lam H (dy n) ∧
      ∀ b ∈ centerOf (centralizerOf (crossedProduct S : Set (L2G H →L[ℂ] L2G H)) (phiHat S)),
        0 ≤ b → b ≤ ((2 * Real.pi : ℝ) : ℂ) • (1 : L2G H →L[ℂ] L2G H) →
        NormedSpace.exp (Complex.I • b) = lam H (dy n) → b = bOp H n := by sorry

end HaagerupReduction.Dyadic
