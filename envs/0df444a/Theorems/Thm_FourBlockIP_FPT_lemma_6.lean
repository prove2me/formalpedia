-- Prove2me | Theorems.Thm_FourBlockIP_FPT_lemma_6
-- name    : FourBlockIP.FPT.lemma_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:40:58.792975+00:00
-- url     : https://prove2.me/theorems/e4e9d010-962a-4b8f-bd50-ca1321d29208
-- title:
--   Lemma 6 — costed global-variable optimization framework
-- statement:
--   There is an absolute natural constant $a\ge2$, fixed before all the following data. Fix natural dimensions $m,n,p$, natural $U$, a positive integer $M$, an integer matrix $A\in\mathbb Z^{m\times n}$, a function $T_{\rm opt}:\mathbb N\to\mathbb N$, a natural $T_{\rm mul}$, and programs $P_{\rm opt},P_{\rm mul}$. Assume:
--
--   1. For every offset $r\in\mathbb Z^m$, every linear subspace $S$ of dimension at most $p$, and every separable convex $\bar f:\mathbb R^{n+m}\to\mathbb R\cup\{+\infty\}$ whose undilated value function (8) is finite at every integer right-hand side, the function $h(z)=\inf\{\bar f(\bar x):[A,I]\bar x=r+Mz,\bar x\in\mathbb Z^{n+m}\}$ is convex extensible on $\mathbb Z^m\cap S$, with an extension never taking $-\infty$.
--
--   2. For every finite separable convex objective $\bar f$, integer bounds $\bar l,\bar u$, integer right-hand side $b$, feasible starting vector $\bar x_0$ for $[A,I]\bar x=b$, and natural $\sigma\ge\|\bar u-\bar l\|_\infty$, the program $P_{\rm opt}$ with $\bar f$'s comparison oracle halts within $T_{\rm opt}(\sigma)$ operations and returns an attained optimum of the bounded subproblem.
--   3. On every integer vector $x$, $P_{\rm mul}$ halts within $T_{\rm mul}$ operations and returns $Ax$.
--   4. Every row sum $\sum_j|A_{ij}|$ is at most $U$.
--
--   Then a program $P$ exists, chosen before the optimization input. For every natural $\ell$, integer $C,l,u,b$, real $V,w,c_0$, and $\rho>0$ satisfying
--
--   $$\{y\in\mathbb R^p:Vy\le w\}\subseteq\{y:|y_j-(c_0)_j|\le\rho\text{ for all }j\},$$
--
--   and every convex $g:\mathbb R^p\to\mathbb R$ and finite separable convex $f:\mathbb R^n\to\mathbb R$, the program with the comparison oracle for $g(y)+f(x)$ solves
--
--   $$\min\{g(y)+f(x):Cy+Ax=b,\ Vy\le w,\ y\in\mathbb Z^p,\ l\le x\le u,\ x\in\mathbb Z^n\}.$$
--
--   Writing $D=\|u-l\|_\infty$ and $L=\log_2(\rho+2)$, its halting cost is at most
--
--   $$aM^p2^{a p^2\lfloor\log_2(p+2)\rfloor}\bigl(L^a+L[T_{\rm opt}((1+2U)D)+T_{\rm mul}+m+\ell]\bigr).$$
--
--   It reports $[0]$ exactly for infeasibility, and otherwise returns a leading $1$ followed by an attained optimal pair $(y,x)$. This is an algorithmic framework with costed subroutines; it retains arbitrary real data, $p=0$, all feasibility and optimality clauses, and the original $M^p$ dependence.
--
--   Differences from the source:
--   - generalization: extension hypothesis for every separable extended convex objective → extension hypothesis only for objectives whose value function (8) is everywhere finite; reason: R4: p. 8 explicitly says the proof uses only these objectives; for n at least one the linear objective -x1 otherwise yields negative infinity and makes the printed strict hypothesis unsatisfiable
--   - reading: asymptotic logarithms of rho and p in runtime bounds → log2(rho+2), floor(log2(p+2)), and an absolute multiplicative constant a at least two; reason: saturated logarithms specify the small-input cases with the same large-input asymptotic dependence
--   - reading: g and f both accessible through a comparison oracle on the joint integer domain → one comparison oracle for the sum g(y)+f(x); reason: the common domain in (7) permits comparing total objectives; separate order oracles do not in general compare a sum
--   - reading: costed optimization and multiplication routines and arithmetic-operation time → restricted RAM programs Popt and Pmul, and a uniform final program, with unit-cost vector comparisons and exact real arithmetic, floor and indirect real memory; reason: R2: every computation is charged on the same machine; variable-length arbitrary real input requires indirect real reads and writes, with no objective values or bit-size guarantee
--   - encoding: vectors in Euclidean spaces and horizontal concatenation [A,I] → ordered Fin coordinates, explicit row-major input lists and attained-optimum output lists; reason: these fixed layouts change no mathematical instance; identity columns follow the columns of A
-- source:
--   Martin Koutecký, Alexandra Lassota, Koen Ligthart, 4-Block Integer Programming is in FPT, STOC 2027 submission #392 (October 2026), Lemma 6, p. 7; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/392.pdf

import Mathlib
import Definitions.Def_FourBlockIP_FPT_Framework

namespace FourBlockIP.FPT

/-- Lemma 6, p. 7. R4 restricts the value-function hypothesis to objectives
for which (8) is everywhere finite. All runtime and correctness clauses are retained.
The absolute constant precedes all framework data, including the subroutines. -/
theorem lemma_6 : ∃ c : ℕ, 2 ≤ c ∧
    ∀ (m n p U M : ℕ) (A : Matrix (Fin m) (Fin n) ℤ)
    (Topt : ℕ → ℕ) (Tmul : ℕ) (Popt Pmul : Program) (hM : 1 ≤ M)
    (h1 : ∀ (r : Fin m → ℤ) (S : Submodule ℝ (Fin m → ℝ)),
      Module.finrank ℝ S ≤ p → ∀ fbar : SepConvexExt (n+m),
        EverywhereFinite (augment A) fbar →
        ConvexExtensibleOn (valueFn (augment A) fbar r M) {z | castVec z ∈ S})
    (h2 : ∀ (lbar ubar : Fin (n+m) → ℤ) (b : Fin m → ℤ)
      (fbar : (Fin (n+m) → ℝ) → ℝ), SepConvex fbar →
      ∀ (sigma : ℕ) (x0 : Fin (n+m) → ℤ),
      eqBoxFeasible (augment A) lbar ubar b x0 → domainLength lbar ubar ≤ sigma →
      ∃ t, halted Popt (run Popt (vectorOracle fbar) (optInput A lbar ubar b x0) [] t) = true ∧
        (run Popt (vectorOracle fbar) (optInput A lbar ubar b x0) [] t).cost ≤ Topt sigma ∧
        ∃ x, eqBoxOptimal (augment A) lbar ubar b fbar x ∧
          output (run Popt (vectorOracle fbar) (optInput A lbar ubar b x0) [] t) = encodeVec x)
    (h3 : ∀ x : Fin n → ℤ, ∃ t,
      halted Pmul (run Pmul noOracle (mulInput A x) [] t) = true ∧
      (run Pmul noOracle (mulInput A x) [] t).cost ≤ Tmul ∧
      output (run Pmul noOracle (mulInput A x) [] t) =
        encodeVec (fun i => ∑ j, A i j * x j))
    (h4 : ∀ i, (∑ j, (A i j).natAbs) ≤ U),
    ∃ P : Program, ∀ (ell : ℕ) (C : Matrix (Fin m) (Fin p) ℤ)
      (l u : Fin n → ℤ) (b : Fin m → ℤ)
      (V : Matrix (Fin ell) (Fin p) ℝ) (w : Fin ell → ℝ)
      (center : Fin p → ℝ) (rho : ℝ), 0 < rho →
      (∀ y : Fin p → ℝ, (∀ i, (∑ j, V i j * y j) ≤ w i) →
        ∀ j, |y j - center j| ≤ rho) →
      ∀ (g : (Fin p → ℝ) → ℝ) (f : (Fin n → ℝ) → ℝ),
      ConvexOn ℝ Set.univ g → SepConvex f →
      ∃ t,
        let st := run P (vectorOracle (mixedObjective g f))
          (frameworkInput ell A C l u b) (frameworkRealInput V w center rho) t
        halted P st = true ∧
        (st.cost : ℝ) ≤ frameworkBound c p M U Topt Tmul m ell (domainLength l u) rho ∧
        mixedCorrect A C l u b V w g f (output st) := by sorry

end FourBlockIP.FPT
