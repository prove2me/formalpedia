-- Prove2me | Theorems.Thm_OffloadGNEP_Mono_Supplement_theorem_3
-- name    : OffloadGNEP.Mono.Supplement.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T21:18:40.224372+00:00
-- url     : https://prove2.me/theorems/f97418c6-86a5-4e51-bea9-18e0ca9056b4
-- title:
--   Theorem 3 (corrected: (24) suffices for uniqueness and Algorithm 1, only some ᾱ for Algorithm 2; constants α/2, 1/α; F_e monotone; load < 1) — Algorithms 1–2 converge
-- statement:
--   Consider the offloading game of Cardellini et al. with $N$ users, $n$ cloudlet servers, offloadable fraction $\chi$ and utilization cap $U_{\max}$. Assume Assumption A ($0<U_{\max}<1$ and $0<\alpha_u,\delta_u<1$ for every user), $n\ge1$ and $0<\chi\le1$. Assume also that the cloudlet load $\frac1n\sum_v\delta_v x_{v,clet}$ is smaller than $1$ for every $x\in\prod_u\tilde K_u$. Let $K_e=(\prod_u\tilde K_u)\times\mathbb R_+$ and $F_e$ be the extended game's set and VI map, and assume that the extended game is monotone, i.e. $F_e$ is monotone on $K_e$ (the setting of §6). Let
--   $$\bar\alpha=\frac{3N}{n}\,\frac{\delta_{\max}}{(1-U_{\max})^3},\qquad \delta_{\max}=\max_u\delta_u .$$
--   Then:
--
--   1. for every $\alpha>\bar\alpha$ and every prox centre $c\in K_e$, $\mathrm{VI}(K_e,F_e+\alpha(\cdot-c))$ has exactly one solution;
--   2. for every $\alpha>\bar\alpha$, every $c\in K_e$ and every $(x^i,\rho^i)\in K_e$, the Jacobi step (S.2)–(S.3) of Algorithm 2 is well defined: it has exactly one result;
--   3. for every $\alpha>\bar\alpha$, every run of Algorithm 1 converges to some solution of $\mathrm{VI}(K_e,F_e)$;
--   4. there is a threshold $\hat\alpha>0$ such that for every $\alpha>\hat\alpha$ and every $c\in K_e$, every run of Algorithm 2 with prox centre $c$ converges to the solution of $\mathrm{VI}(K_e,F_e+\alpha(\cdot-c))$.
--
--   Since every iterate of Algorithm 1 lies in $K_e$, assertion 4 covers the inner problem of every outer iteration $k$. Assertion 3 is Algorithm 1 with its subproblems solved exactly, which by assertions 1 and 4 is the limit Algorithm 2 computes. Together, for every $\alpha>\max\{\bar\alpha,\hat\alpha\}$, they give the theorem's "there exists a positive $\bar\alpha$". The explicit value (24) is not claimed for Algorithm 2: it is false there (see the differences below). Through Theorem 2, a solution of $\mathrm{VI}(K_e,F_e)$ yields a variational solution of the offloading GNEP, so the theorem gives a distributed method that computes one.
--
--   **Formalization Note** The Algorithm 2 step is a relation: each user's new strategy minimises its (S.2) objective over $\tilde K_u$ with the Euclidean norm written out, and the price is the (S.3) formula. Convergence is in the product topology on $\mathbb R^{3N}\times\mathbb R$. Users are indexed from $0$.
--
--   Differences from the source:
--   - correction: Algorithm 2 (S.2) uses α‖x_u − x_u^k‖² and (S.3) uses ρ^k + (1/(2α))(load − U_max) → (α/2)‖x_u − x_u^k‖² and ρ^k + (1/α)(load − U_max); reason: with the printed constants the iteration's fixed points solve VI(K_e, F_e + 2α(· − (x^k,ρ^k))), not the VI with α named by Algorithm 1, the theorem and the Jacobian (25) on p. 18; the printed scheme with parameter α is the repaired scheme with parameter 2α
--   - correction: Assumption A and the standing hypotheses → in addition, load(x) = (1/n)Σ_v δ_v x_{v,clet} < 1 for every x ∈ Π_u K̃_u; reason: the users' costs, F and F_e divide by 1 − load, and on K_e = (Π_u K̃_u) × R₊ Assumption A does not keep load below 1 (N = 2, n = 1, χ = 1, δ_u = 0.9, x_u = (0,1,0) gives load 1.8), so the printed algorithms evaluate undefined or meaningless costs; the cases excluded are exactly the instances in which some point of K_e has load ≥ 1; (18) implies the guard, and the published Theorem 2 uses the same one
--   - correction: the theorem states no monotonicity → F_e is monotone on K_e; reason: §6 works "under the conditions of Theorem 1" (p. 15), p. 16 says the extended game "is monotone ... in particular, if the conditions of Theorem 1 are met" and builds §6 on it, and the convergence of Algorithm 1 is taken from [17, Chapter 12] (p. 17), the proximal-point theory of monotone VIs; (18) itself only gives monotonicity on K, not on K_e (Theorem 1), so the property §6 uses is stated; excluded: instances where F_e is not monotone on K_e, e.g. N = 2, n = 1, χ = 1, δ = (0.8, 0.1), where at x_clet = (1, 0) the symmetric Jacobian block is indefinite
--   - correction: "in particular, we can take ᾱ = (24)" for the convergence of Algorithm 2 → some ᾱ > 0 (depending on the data); reason: (24) is false for Algorithm 2: N = 3, n = 1, χ = 1, δ_u = 3/10, U_max = 1/10 (so (18) holds and F_e is monotone on K_e), α_u = 1/2, β_u = 1, γ_u = 10, P_m = 10, P_t = P_max = 1, α = 19/5 > ᾱ = 100/27, centre x^k_u = (0, 49/50, 1/50), ρ^k = 0: the run from x_u = (0,1,0), ρ = 1/5 alternates between x_{u,clet} = 1 and x_{u,clet} < 24/25, with either the repaired or the printed constants (DISPROOF.md); the proof bounds B_uv over K_e using D ≥ 1 − U_max, which holds only on K; the value (24) is kept for uniqueness, well-posedness and Algorithm 1
--   - reading: Algorithm 1 with every subproblem solved by Algorithm 2 → assertion 4 (Algorithm 2 converges to the unique regularized solution, for every prox centre in K_e) and assertion 3 (Algorithm 1 with exactly solved subproblems converges); reason: Algorithm 2 reaches the subproblem's solution only in the limit, and its limit is the exact subproblem solution that Algorithm 1's (S.2) prescribes
--   - reading: for every k → for every prox centre c ∈ K_e; reason: every outer iterate lies in K_e, so this covers every k of every run
--   - reading: (S.2) asks for the unique solution of a strongly convex problem → assertion 2 states that the Jacobi step exists and is unique from every point of K_e; reason: this is the well-posedness the algorithm asserts, and it keeps assertion 4 from being vacuous
--   - reading: stopping tests (S.1) of both algorithms → not encoded, runs are infinite sequences; reason: a solution is a fixed point of each update, so a stopped run corresponds to a constant tail
--   - encoding: users u = 1,…,N and ‖·‖ on R³ → Fin N (0-based) and the Euclidean norm written as a sum of squares; reason: Lean conventions; same instances
-- source:
--   Cardellini et al., A game-theoretic approach to computation offloading in mobile cloud computing, accepted manuscript (IRIS Sapienza 11573/779661; DOI 10.1007/s10107-015-0881-6), p. 17, Theorem 3 and (24); Algorithms 1 and 2, p. 17; §6 setting, pp. 15–17

import Mathlib
import Definitions.Def_OffloadGNEP_Mono_Supplement_Algorithms

namespace OffloadGNEP.Mono.Supplement

open OffloadGNEP.Ext Filter Topology

theorem theorem_3 {N : ℕ} (P : Params N) (hA : P.AssumptionA) (hS : P.Standing)
    (hD : ∀ x ∈ Kprod P, load P x < 1) (hM : IsMonotoneOnE (Ke P) (Fe P)) :
    (∀ α : ℝ, alphaBar P < α →
      (∀ c ∈ Ke P, ∃! p, IsVISolE (Ke P) (regMap P α c) p) ∧
      (∀ c ∈ Ke P, ∀ z ∈ Ke P, ∃! z', IsAlg2Step P α c z z') ∧
      (∀ t, IsAlg1Run P α t →
        ∃ z, IsVISolE (Ke P) (Fe P) z ∧ Tendsto t atTop (𝓝 z))) ∧
    ∃ αbar : ℝ, 0 < αbar ∧ ∀ α : ℝ, αbar < α →
      ∀ c ∈ Ke P, ∀ s, IsAlg2Run P α c s →
        ∀ p, IsVISolE (Ke P) (regMap P α c) p → Tendsto s atTop (𝓝 p) := by sorry

end OffloadGNEP.Mono.Supplement
