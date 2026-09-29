-- Prove2me | Theorems.Thm_MarkovMixing_relaxation_upper_aperiodic
-- name    : MarkovMixing.relaxation_upper_aperiodic
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-22T16:29:17.95806+00:00
-- url     : https://prove2.me/theorems/62258486-e9e7-4014-9c37-6f326a309977
-- title:
--   Theorem 12.3 -- mixing is at most relaxation times a log factor
-- statement:
--   Let $P$ be a Markov chain on a finite state space $V$ that is **irreducible** (from any state, any other state is reachable in some number of steps), **aperiodic** (the return times to each state have greatest common divisor $1$), and **reversible** with respect to its stationary distribution $\pi$, meaning the detailed balance equations $\pi(x)P(x,y)=\pi(y)P(y,x)$ hold for all states $x,y$.
--
--   Call a real number $\lambda$ an *eigenvalue* of $P$ if some function $f:V\to\mathbb R$ that is not identically zero satisfies $Pf=\lambda f$, where $(Pf)(x)=\sum_y P(x,y)f(y)$. Every eigenvalue of a transition matrix lies in $[-1,1]$, and $1$ is always one of them. Let
--   $$\lambda_\star=\max\{|\lambda| : \lambda \text{ an eigenvalue of } P,\ \lambda\neq 1\}$$
--   be the largest modulus of an eigenvalue other than $1$. The **absolute spectral gap** is $\gamma_\star=1-\lambda_\star$ and the **relaxation time** is $t_{\mathrm{rel}}=1/\gamma_\star$. For an irreducible aperiodic chain $\gamma_\star>0$, so $t_{\mathrm{rel}}$ is a finite number — this is exactly what aperiodicity buys: a periodic chain has $-1$ as an eigenvalue, hence $\lambda_\star=1$ and no finite relaxation time.
--
--   Two more quantities. The **total variation distance** between two probability distributions $\mu,\nu$ on $V$ is $\|\mu-\nu\|_{TV}=\max_{A\subseteq V}|\mu(A)-\nu(A)|$, the largest discrepancy they assign to any event. Writing $d(t)=\max_{x\in V}\|P^t(x,\cdot)-\pi\|_{TV}$ for the worst-case distance from stationarity after $t$ steps, the **mixing time** is the first time this drops to $\varepsilon$:
--   $$t_{\mathrm{mix}}(\varepsilon)=\min\{t\in\mathbb N : d(t)\le\varepsilon\}.$$
--   Finally $\pi_{\min}=\min_{x\in V}\pi(x)$ is the smallest stationary weight.
--
--   **The theorem** (Levin–Peres–Wilmer, Theorem 12.3) asserts that for every tolerance $0<\varepsilon<1$,
--   $$t_{\mathrm{mix}}(\varepsilon)\;\le\;\log\!\Bigl(\frac{1}{\varepsilon\,\pi_{\min}}\Bigr)\,t_{\mathrm{rel}}\;+\;1 .$$
--
--   In words: mixing costs at most a factor $\log(1/(\varepsilon\pi_{\min}))$ more than relaxation, so a bound on the spectral gap immediately yields a bound on the mixing time. The additive $1$ absorbs the rounding of the real-valued right-hand side to an integer time. The companion result, Theorem 12.4, supplies the matching lower bound $t_{\mathrm{mix}}(\varepsilon)\ge(t_{\mathrm{rel}}-1)\log(1/2\varepsilon)$, so for reversible chains the mixing time is pinned between $t_{\mathrm{rel}}$ and $t_{\mathrm{rel}}\log(1/\pi_{\min})$.
--
--   *A note on the aperiodicity hypothesis.* Levin–Peres–Wilmer state Theorem 12.3 for a reversible irreducible chain, reading $t_{\mathrm{rel}}=1/\gamma_\star$ in $(0,\infty]$: for a periodic chain $\gamma_\star=0$, the right-hand side is $+\infty$, and the inequality asserts nothing. Division is total in Lean, where $1/0$ evaluates to $0$, so that empty case would instead *collapse* the bound to the false claim $t_{\mathrm{mix}}(\varepsilon)\le 1$ — simple random walk on the path $0-1-2-3$ is reversible and irreducible with $t_{\mathrm{mix}}(3/5)=2$. Aperiodicity is therefore hypothesized: it is precisely the condition under which the book's right-hand side is finite, and it is the hypothesis the companion Theorem 12.4 already carries.
-- source:
--   D. A. Levin, Y. Peres, E. L. Wilmer, Markov Chains and Mixing Times, AMS 2009, https://documents.epfl.ch/groups/i/ip/ipg/www/2013-2014/Random_Walks/markovmixing.pdf, Section 12.2, Theorem 12.3, Eq. (12.9), p. 155

import Definitions.Def_mm_spectral
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace MarkovMixing

/-- **Theorem 12.3** (LPW): for a reversible irreducible chain,
`t_mix(ε) ≤ log(1/(ε π_min)) · t_rel + 1`.

LPW state this for a reversible irreducible chain, reading `t_rel = 1/γ⋆` in
`(0, ∞]`: when the chain is periodic `λ⋆ = 1`, the right-hand side is `+∞` and
the inequality has no content.  Real division in Lean is total (`0⁻¹ = 0`), so
that vacuous case would instead *collapse* the bound to `t_mix(ε) ≤ 1`, which
is false — simple random walk on the path `0-1-2-3` has `t_mix(3/5) = 2`.
Aperiodicity is therefore hypothesized, exactly the condition under which the
book's `t_rel` is finite (Lemma 12.1(iii) gives `γ⋆ > 0`), matching the
companion lower bound `relaxation_lower` (Theorem 12.4). -/
theorem relaxation_upper_aperiodic {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (P : Matrix V V ℝ) (hP : IsStochastic P) (hirr : Irreducible P)
    (hap : Aperiodic P)
    (π : V → ℝ) (hπ : IsStationary P π) (hrev : DetailedBalance P π)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    (mixingTime P π ε : ℝ) ≤
      Real.log (1 / (ε * ⨅ x : V, π x)) * relaxationTime P + 1 := by
  sorry

end MarkovMixing
