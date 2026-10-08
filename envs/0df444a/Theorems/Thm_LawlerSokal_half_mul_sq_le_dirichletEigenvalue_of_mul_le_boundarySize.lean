-- Prove2me | Theorems.Thm_LawlerSokal_half_mul_sq_le_dirichletEigenvalue_of_mul_le_boundarySize
-- name    : LawlerSokal.half_mul_sq_le_dirichletEigenvalue_of_mul_le_boundarySize
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-04T11:31:24.449351+00:00
-- url     : https://prove2.me/theorems/4bc068f9-2384-4d74-8344-b899a45ab2fc
-- title:
--   Lawler–Sokal, Theorem 3.1 (Cheeger’s inequality, as Erschler–Zheng apply it) — |∂U| ≥ h·π(U) for every non-empty U ⊆ Ω gives λ₁(Ω) ≥ h²/2
-- statement:
--   Let $X$ be a countable set, $P$ a transition kernel on $X$ (`IsTransition P`: $P(x,y) \ge 0$, and every row is summable with $\sum_y P(x,y) = 1$), and $\pi : X \to \mathbb R$ a weight with $\pi(x) > 0$ for every $x$, such that $P$ is reversible with respect to $\pi$ (`IsReversible P π`: $\pi(x)P(x,y) = \pi(y)P(y,x)$). Let $\Omega$ be a finite non-empty subset of $X$, and $h \ge 0$ a real number such that, for every non-empty $U \subseteq \Omega$,
--   $$h \sum_{x\in U}\pi(x) \le |\partial_P U|,$$
--   where $|\partial_P U| = \sum_{x\in U}\sum_{y\notin U}\pi(x)P(x,y)$ (`boundarySize P π U`). Then
--   $$\tfrac12 h^2 \le \lambda_1(\Omega),$$
--   where $\lambda_1(\Omega)$ (`dirichletEigenvalue P π Ω`) is the infimum of $\mathcal E_P(f) = \frac12\sum_{x,y\in X}(f(x)-f(y))^2P(x,y)\pi(x)$ over the real functions $f$ that vanish outside $\Omega$ and have $\sum_x f(x)^2\pi(x) = 1$.
--
--   The condition on $h$ includes $U = \Omega$, and $|\partial_P U|$ counts the flow from $U$ to all of $X \setminus U$, to the rest of $\Omega$ as well as out of $\Omega$. The weight $\pi$ need not be summable or normalized, and $P$ need not be irreducible. Under these hypotheses $\lambda_1(\Omega)$ is a genuine infimum, of a non-empty set of numbers $\ge 0$.
--
--   G. F. Lawler and A. D. Sokal, *Bounds on the $L^2$ spectrum for Markov chains and Markov processes: a generalization of Cheeger’s inequality*, Trans. Amer. Math. Soc. 309 (1988) 557–580, [doi:10.1090/S0002-9947-1988-0930082-9](https://doi.org/10.1090/S0002-9947-1988-0930082-9), consider a jump process with transition rate kernel $J(x,dy)$, killing rate $K(x) \ge 0$ and generator $L$, and state on p. 565: “**Theorem 3.1.** Let $L$ be a selfadjoint operator on $L^2(\pi)$ whose associated sesquilinear form is given by (3.7), where $\mu$ is a symmetric positive measure whose marginals are $\le [M - \frac12K(x)]\pi(dx)$. Then (3.12) $h^2/2M \le \lambda_0(L) \le h$, where $h$ is defined by (3.3), (3.4b).” The constant and the spectral bottom are defined on p. 564: “(3.3) $h \equiv \inf_{\substack{A\in\mathscr S\\ \pi(A)>0}} h(A)$ with (3.4a) $h(A) \equiv \frac{\int\pi(dx)\chi_A(x)[J(x,A^c) + K(x)]}{\pi(A)}$”, and “(3.5) $\lambda_0(L) \equiv \inf\mathrm{spec}(L)$.” By p. 560, the results for discrete-time chains “follow immediately as a special case (just put $M = 1$).”
--
--   A. Erschler and T. Zheng, *Growth of periodic Grigorchuk groups*, Invent. Math. 219 (2020) 1069–1155, [doi:10.1007/s00222-019-00922-0](https://doi.org/10.1007/s00222-019-00922-0), with the page numbers of [arXiv:1802.09077v2](https://arxiv.org/abs/1802.09077v2), write on p. 24: “By Cheeger’s inequality (see [37, Theorem 3.1]) (5.1) $\lambda_1(\Omega) \geqslant \frac12\left(\frac{|\partial_P\Omega|}{\pi(\Omega)}\right)^2$, where $|\partial_P\Omega| = \sum_{x\in\Omega,y\in\Omega^c}\pi(x)P(x,y)$ is the size of the boundary of $\Omega$ with respect to $(P,\pi)$.” In the proof of Lemma 5.2 (p. 25) they show, “for any set $U \subset o\cdot G$ with $|U| \leqslant \frac{c_0}{2}|F_n|$, $\frac{|\partial_{P_n}U|}{|U|} \geqslant \frac{c_0}{4}$”, and conclude: “By Cheeger’s inequality (5.1), the $\ell^2$-isoperimetric profile of $P_n$ satisfies $\Lambda_{P_n}(v) \geqslant \frac12\left(\frac{c_0}{4}\right)^2$ for all $v \leqslant \frac{c_0}{2}|F_n|$.” The proof of Proposition 7.19 (p. 48) argues the same way from “$\frac{|\partial_{P_n}U|}{|U|} \geqslant \frac12$” for every $U$ with $|U| \leqslant 2^{n-1}$.
--
--   Both applications bound the boundary ratio of every set of bounded size. So for each finite $\Omega$ in the infimum that defines $\Lambda(v)$ they bound it for every non-empty $U \subseteq \Omega$, and this statement is (5.1) in that form. As printed, (5.1) bounds $\lambda_1(\Omega)$ by the ratio $|\partial_P\Omega|/\pi(\Omega)$ of $\Omega$ alone, and that version fails (`ErschlerZhengPrinted.exists_dirichletEigenvalue_lt_half_mul_sq_boundarySize_div`); Lawler and Sokal’s $h$ is an infimum over subsets.
--
--   Lawler and Sokal’s Corollary 3.2 (p. 567) is their version for a process killed when it leaves a subset $B$ of the state space $S$: it bounds $\lambda_0(L_B)$ below by $h_B^2/2M$, where “(3.21) $h_B = \inf_{A\subset B,\ \pi(A)>0} h(A)$” and, by (3.22a), $h(A)$ is the flow from $A$ to $S \setminus A$ divided by $\pi(A)$; for a discrete-time chain that ratio is $|\partial_P A|/\pi(A)$. This statement is (5.1) read through that corollary, with $B = \Omega$, $M = 1$ and $\lambda_0(L_B)$ read as $\lambda_1(\Omega)$; its hypothesis bounds $|\partial_P U|/\pi(U)$ below by $h$ for every non-empty $U \subseteq \Omega$. Lawler and Sokal’s §3 is set up for a process that is “positive-recurrent with finite invariant measure $\pi$” (p. 564), and Erschler and Zheng’s $\pi \equiv 1$ on an infinite orbit is not a finite measure; this statement asks only $\pi > 0$ and reversibility.
--
--   The proof here does not go through Lawler and Sokal’s theorem; it is the direct argument, with no spectral theory. Let $f$ vanish outside $\Omega$ with $\sum_x f(x)^2\pi(x) = 1$, and let $a = |f|$. A layer-cake induction over the superlevel sets of $a^2$, which are subsets of $\Omega$ where the hypothesis applies, gives $h \le \sum_{x\in\Omega}\pi(x)\sum_y P(x,y)\,(a(x)^2-a(y)^2)_+$. Writing $a(x)^2 - a(y)^2 = (a(x)-a(y))(a(x)+a(y))$, the AM–GM inequality bounds this by $\frac1h\sum_{x\in\Omega}\pi(x)\sum_y P(x,y)\,(a(x)-a(y))_+^2 + \frac h2$, the second term through reversibility and $\sum_y P(x,y) \le 1$. By reversibility the sum in the first term is $\mathcal E_P(a)$, and $\mathcal E_P(a) \le \mathcal E_P(f)$. So $h \le \mathcal E_P(f)/h + h/2$ when $h > 0$, that is $\frac12h^2 \le \mathcal E_P(f)$.
-- source:
--   G. F. Lawler and A. D. Sokal, Bounds on the L² spectrum for Markov chains and Markov processes: a generalization of Cheeger's inequality, Trans. Amer. Math. Soc. 309 (1988) 557–580, https://doi.org/10.1090/S0002-9947-1988-0930082-9, Theorem 3.1, as applied in A. Erschler and T. Zheng, Growth of periodic Grigorchuk groups, Invent. Math. 219 (2020) 1069–1155, https://doi.org/10.1007/s00222-019-00922-0 (arXiv:1802.09077v2, whose page numbers are used), p. 24, (5.1) (in the proofs of Lemma 5.2, p. 25, and Proposition 7.19, p. 48)

import Mathlib
import Definitions.Def_DurrettProbability_MarkovChain
import Definitions.Def_MarkovChain_HeatKernels

open DurrettProbability MarkovChain

namespace LawlerSokal

theorem half_mul_sq_le_dirichletEigenvalue_of_mul_le_boundarySize {X : Type*} [Countable X]
    (P : X → X → ℝ) (π : X → ℝ) (hP : IsTransition P) (hπ : ∀ x, 0 < π x)
    (hrev : IsReversible P π) (Ω : Finset X) (hΩ : Ω.Nonempty) (h : ℝ) (hh : 0 ≤ h)
    (hbd : ∀ U ⊆ Ω, U.Nonempty → h * ∑ x ∈ U, π x ≤ boundarySize P π U) :
    1 / 2 * h ^ 2 ≤ dirichletEigenvalue P π Ω := by
  sorry

end LawlerSokal
