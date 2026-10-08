-- Prove2me | Theorems.Thm_MPECRelax_KDBConv_display_11_13_14
-- name    : MPECRelax.KDBConv.display_11_13_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T07:50:04.606894+00:00
-- url     : https://prove2.me/theorems/8d6965eb-c59d-40d8-b7aa-4618334c6eb8
-- title:
--   Proof of Theorem 3.5, p. 15, (11), (13), (14) — KKT conditions of R^KDB(t) rewritten with η^G, η^H
-- statement:
--   Let the data of the MPEC (1) be continuously differentiable, let $t>0$, and let $x$ be a point with KKT multipliers for the relaxed program $R^{KDB}(t)$: $\lambda\in\mathbb R^m$, $\alpha,\beta,\gamma\in\mathbb R^l$ for the constraints $g_i\le 0$, $G_i\ge -t$, $H_i\ge -t$, $(G_i-t)(H_i-t)\le 0$, and $\mu\in\mathbb R^p$ for $h=0$. Put
--   $$\eta^G_i:=-\gamma_i(H_i(x)-t),\qquad \eta^H_i:=-\gamma_i(G_i(x)-t)\qquad(i=1,\dots,l).$$
--   Then
--   $$0=\nabla f(x)+\sum_{i=1}^m\lambda_i\nabla g_i(x)+\sum_{j=1}^p\mu_j\nabla h_j(x)-\sum_{i=1}^l\alpha_i\nabla G_i(x)-\sum_{i=1}^l\beta_i\nabla H_i(x)-\sum_{i=1}^l\eta^G_i\nabla G_i(x)-\sum_{i=1}^l\eta^H_i\nabla H_i(x),\tag{11}$$
--   and, writing $\operatorname{supp}(z)=\{i\mid z_i\ne 0\}$,
--
--   1. $\operatorname{supp}(\alpha)\cap\operatorname{supp}(\eta^G)=\emptyset$, $\operatorname{supp}(\beta)\cap\operatorname{supp}(\eta^H)=\emptyset$, $\operatorname{supp}(\eta^G)\cap\operatorname{supp}(\eta^H)=\emptyset$; (13)
--   2. if $i\in\operatorname{supp}(\eta^G)\cap\operatorname{supp}(\beta)$ then $\eta^G_i>0$, and if $i\in\operatorname{supp}(\eta^H)\cap\operatorname{supp}(\alpha)$ then $\eta^H_i>0$. (14)
--
--   In the paper, $x=x^k$, $t=t_k$ and the multipliers carry the index $k$. The identity (11) recasts the stationarity condition of the relaxed program in the form of the MPEC's weak-stationarity equation; (13) and (14) are the sign and support information that later yields M-stationarity in the limit.
--
--   **Formalization Note** The paper's proof skips the standard constraints $g$, $h$; here they are kept, so (11) contains the terms $\sum\lambda_i\nabla g_i+\sum\mu_j\nabla h_j$. The multipliers are the blocks of a multiplier vector of $R^{KDB}(t)$ in the sense of the mission's NLP encoding (constraints $-(G_i+t)\le0$, $-(H_i+t)\le0$, $(G_i-t)(H_i-t)\le0$). Feasibility of $x$ is not needed for these three displays; $t>0$ is.
-- source:
--   Hoheisel, Kanzow, Schwartz, Theoretical and numerical comparison of relaxation methods for mathematical programs with complementarity constraints, Preprint 299, Univ. Würzburg, Sept. 2010, p. 15, proof of Theorem 3.5, displays (11), (13), (14)

import Mathlib
import Definitions.Def_MPECRelax_KDBConv_Basic

open Filter Topology

namespace MPECRelax.KDBConv

/-- Proof of Theorem 3.5, p. 15, displays (11), (13), (14). Let `t > 0`, and let
`(Λ, mu)` be KKT multipliers of R^KDB(t) at `x`, with `λ = kdbLam Λ`, `α = kdbAlpha Λ`,
`β = kdbBeta Λ`, `γ = kdbGamma Λ`, and put `η^G_i = −γ_i (H_i(x) − t)`,
`η^H_i = −γ_i (G_i(x) − t)`. Then (11) holds (with the standard constraints `g`, `h`
kept), the supports satisfy the disjointness relations (13), and the sign relations (14)
hold. -/
theorem display_11_13_14 {n m p l : ℕ} (P : MPEC n m p l) (hP : P.IsC1)
    (t : ℝ) (ht : 0 < t) (x : MPECRelax.ScholtesConv.E n)
    (Λ : Fin m ⊕ Fin l ⊕ Fin l ⊕ Fin l → ℝ) (mu : Fin p → ℝ)
    (hKKT : (P.RKDB t).KKTMult x Λ mu) :
    (gradient P.f x + ∑ i, MPEC.kdbLam Λ i • gradient (P.g i) x
        + ∑ j, mu j • gradient (P.h j) x
        - ∑ i, MPEC.kdbAlpha Λ i • gradient (P.G i) x
        - ∑ i, MPEC.kdbBeta Λ i • gradient (P.H i) x
        - ∑ i, P.etaG x t (MPEC.kdbGamma Λ) i • gradient (P.G i) x
        - ∑ i, P.etaH x t (MPEC.kdbGamma Λ) i • gradient (P.H i) x = 0) ∧
    (Function.support (MPEC.kdbAlpha Λ) ∩ Function.support (P.etaG x t (MPEC.kdbGamma Λ)) = ∅ ∧
      Function.support (MPEC.kdbBeta Λ) ∩ Function.support (P.etaH x t (MPEC.kdbGamma Λ)) = ∅ ∧
      Function.support (P.etaG x t (MPEC.kdbGamma Λ)) ∩
        Function.support (P.etaH x t (MPEC.kdbGamma Λ)) = ∅) ∧
    ((∀ i ∈ Function.support (P.etaG x t (MPEC.kdbGamma Λ)) ∩ Function.support (MPEC.kdbBeta Λ),
        0 < P.etaG x t (MPEC.kdbGamma Λ) i) ∧
      (∀ i ∈ Function.support (P.etaH x t (MPEC.kdbGamma Λ)) ∩ Function.support (MPEC.kdbAlpha Λ),
        0 < P.etaH x t (MPEC.kdbGamma Λ) i)) := by sorry

end MPECRelax.KDBConv
