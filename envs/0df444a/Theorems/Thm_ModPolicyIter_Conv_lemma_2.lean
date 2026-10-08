-- Prove2me | Theorems.Thm_ModPolicyIter_Conv_lemma_2
-- name    : ModPolicyIter.Conv.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T14:14:00.053033+00:00
-- url     : https://prove2.me/theorems/9a997231-b00e-4d1c-a879-95323bec8763
-- title:
--   Lemma 2, p. 1130 — U^k-iteration converges geometrically to its unique fixed point, which solves Bu = 0
-- statement:
--   Throughout, $S$ is a set of states with a $\sigma$-algebra; each policy $P\in\mathcal P$ is a Markov transition kernel on $S$ with a measurable one-period reward $c_P$, $\sup_P\sup_s|c_P(s)|\le M$; $0\le\lambda<1$; $V$ is the space of bounded measurable functions with $\|v\|=\sup_s|v(s)|$; and the maximum in $Bv=\max_P\{c_P+(\lambda P-I)v\}$ is attained for every $v\in V$, a maximizer being written $P_v$.
--
--   Fix $k\ge 0$ and assume $U^k$ maps $V$ into $V$. Let $u_0\in V$ and $u^k_n=(U^k)^nu_0$. Then there is $u^k\in V$ such that
--
--   1. $u^k$ is the unique fixed point of $U^k$ in $V$ and $\|u^k_n-u^k\|\to 0$;
--   2. for every $n\ge 0$,
--   $$\|u^k_{n+1}-u^k\|\le\lambda^{k+1}\|u^k_n-u^k\|;$$
--   3. $Bu^k=0$.
--
--   In particular all the operators $U^k$ have the same fixed point $u^*$, the solution of the optimality equation.
--
--   **Formalization Note** The hypothesis that $U^k$ maps $V$ into $V$ is the paper's implicit premise (Lemma 1 calls $U^k$ a contraction mapping on $V$ and the proof applies the Banach fixed point theorem in $V$); for $k=0$ it follows from the standing attainment assumption, since a single maximizer gives $U^0v=c_{P_v}+\lambda P_vv$. Part (ii) is stated with indices $n+1,n$ instead of $n,n-1$.
-- source:
--   Puterman and Shin, Modified policy iteration algorithms for discounted Markov decision problems, Management Science 24 (1978), DOI 10.1287/mnsc.24.11.1127, p. 1130, Lemma 2

import Mathlib
import Definitions.Def_ModPolicyIter_Conv_Setting

open MeasureTheory ProbabilityTheory Filter Topology

namespace ModPolicyIter.Conv

/-- Lemma 2 (Puterman–Shin 1978, p. 1130): for `u₀ ∈ V`, the iterates `u^k_n = (U^k)^n u₀`
(i) converge in norm to `u^k`, the unique fixed point of `U^k` in `V`,
(ii) satisfy `‖u^k_{n+1} − u^k‖ ≤ λ^{k+1} ‖u^k_n − u^k‖`, and
(iii) `u^k` solves `Bu = 0`.
`hUV` (`U^k` maps `V` into `V`) is the paper's implicit premise. -/
theorem lemma_2 {S : Type*} [MeasurableSpace S] {ι : Type*} (m : Model S ι)
    (hmax : MaxAttained m) (k : ℕ) (hUV : ∀ w : S → ℝ, IsBM w → IsBM (U m k w))
    (u0 : S → ℝ) (hu0 : IsBM u0) :
    ∃ uk : S → ℝ, IsBM uk ∧ U m k uk = uk ∧
      (∀ w : S → ℝ, IsBM w → U m k w = w → w = uk) ∧
      Tendsto (fun n => supNorm ((U m k)^[n] u0 - uk)) atTop (𝓝 0) ∧
      (∀ n, supNorm ((U m k)^[n + 1] u0 - uk) ≤ m.lam ^ (k + 1) * supNorm ((U m k)^[n] u0 - uk)) ∧
      (∀ s, B m uk s = 0) := by sorry

end ModPolicyIter.Conv
