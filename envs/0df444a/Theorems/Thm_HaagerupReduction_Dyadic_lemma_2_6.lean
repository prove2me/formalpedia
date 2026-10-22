-- Prove2me | Theorems.Thm_HaagerupReduction_Dyadic_lemma_2_6
-- name    : HaagerupReduction.Dyadic.lemma_2_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:28:14.306245+00:00
-- url     : https://prove2.me/theorems/2ab2200a-359d-40c7-8801-b50bd1c94c43
-- title:
--   Lemma 2.6, p. 9 — for x ∈ R: ‖[b_n, x]‖_φ̂ → 0, sup_{|t|≤1} ‖[e^{itb_n}, x]‖_φ̂ → 0, sup_t ‖σ^φ̂_t(x) − e^{ia_nt}xe^{−ia_nt}‖_φ̂ → 0
-- statement:
--   Let $\mathcal R = M\rtimes_{\sigma^\varphi}G$, $\hat\xi$, $b_n$ and $a_n = 2^nb_n$ be as in the model, $\|y\|_{\hat\varphi} = \hat\varphi(y^*y)^{1/2} = \|y\hat\xi\|$, $[y,x] = yx - xy$, and let $\hat S$ be modular data of $(\mathcal R,\hat\varphi)$ ($\hat S.M = \mathcal R$, $\hat S.\xi = \hat\xi$) with modular group $\sigma^{\hat\varphi}$. Then for every $x\in\mathcal R$:
--
--   1. $\displaystyle\lim_{n\to\infty}\|[b_n,x]\|_{\hat\varphi} = 0$;
--   2. $\displaystyle\lim_{n\to\infty}\sup_{t\in[-1,1]}\|[e^{itb_n},x]\|_{\hat\varphi} = 0$;
--   3. $\displaystyle\lim_{n\to\infty}\sup_{t\in\mathbb R}\big\|\sigma^{\hat\varphi}_t(x) - e^{ia_nt}xe^{-ia_nt}\big\|_{\hat\varphi} = 0$.
--
--   Part 3 says that, in the $\hat\varphi$-norm, the modular group of $\hat\varphi$ is uniformly approximated by the inner groups $\operatorname{Ad}e^{ia_nt}$; with (2.4) this gives Lemma 2.7.
--
--   **Formalization Note.** Parts 2 and 3 are written in ε–N form: for every $\varepsilon>0$ there is $N$ with the quantity $\le\varepsilon$ for all $n\ge N$ and all $t$ in the range. This is the same as the limit of the suprema being $0$, and avoids Lean's junk value of a supremum of an unbounded family. Only part 3 uses $\hat S$.
-- source:
--   Haagerup, Junge & Xu, A reduction method for noncommutative Lp-spaces and applications, arXiv:0806.3635v2, p. 9, Lemma 2.6 (proof pp. 10–11); ‖x‖_ψ and [x, y] defined on p. 9

import Mathlib
import Definitions.Def_BoundedRecovery
import Definitions.Def_HaagerupReduction_Dyadic_Model

namespace HaagerupReduction.Dyadic

universe u

open OAI.BoundedRecovery
open Filter Topology

/-- Lemma 2.6: for `x ∈ R`, (i) `‖[b_n, x]‖_φ̂ → 0`; (ii) `sup_{t ∈ [-1,1]} ‖[e^{itb_n}, x]‖_φ̂ → 0`;
(iii) `sup_{t ∈ ℝ} ‖σ^φ̂_t(x) - e^{ia_n t} x e^{-ia_n t}‖_φ̂ → 0`. -/
theorem lemma_2_6 {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (S : StandardModularData H)
    (Sh : StandardModularData (L2G H)) (hM : Sh.M = crossedProduct S) (hxi : Sh.xi = xiHat S)
    (x : L2G H →L[ℂ] L2G H) (hx : x ∈ crossedProduct S) :
    Tendsto (fun n : ℕ => phiNorm S (bOp H n * x - x * bOp H n)) atTop (𝓝 0) ∧
    (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ t ∈ Set.Icc (-1 : ℝ) 1,
      phiNorm S (NormedSpace.exp (((t : ℂ) * Complex.I) • bOp H n) * x -
        x * NormedSpace.exp (((t : ℂ) * Complex.I) • bOp H n)) ≤ ε) ∧
    (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ t : ℝ,
      phiNorm S (Sh.sigma t x - NormedSpace.exp (((t : ℂ) * Complex.I) • aOp H n) * x *
        NormedSpace.exp (-(((t : ℂ) * Complex.I) • aOp H n))) ≤ ε) := by sorry

end HaagerupReduction.Dyadic
