-- Prove2me | Theorems.Thm_KServer_extended_cost_lemma_injective
-- name    : KServer.extended_cost_lemma_injective
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-31T07:20:52.332303+00:00
-- url     : https://prove2.me/theorems/d0391245-e074-4300-b438-9cab3707f207
-- title:
--   Extended Cost Lemma with the growth bound required only at injective configurations
-- statement:
--   Fix a metric space $M$, $k\ge1$ servers and an initial configuration $C_0$, and write $\widehat w_t$ for the unordered work function after the first $t$ requests of a sequence $\sigma$. Call a configuration **injective** when its $k$ servers occupy $k$ distinct points.
--
--   **Statement.** Suppose an injective configuration $X_0$ exists, and that for constants $\lambda,c$ every request sequence of length $m$ admits numbers $u_1,\dots,u_m$ with
--   $$\widehat w_t(X)\;\le\;\widehat w_{t-1}(X)+u_t\quad\text{for every \emph{injective} configuration }X\text{ and every }t\le m,$$
--   $$\sum_{t=1}^{m}u_t\;\le\;\lambda\cdot\mathrm{OPT}(C_0,\sigma)+c .$$
--   Then there is an online algorithm starting at $C_0$ which is $(\lambda-1)$-competitive.
--
--   **Role.** This is the Extended Cost Lemma of Chrobak and Larmore in the form the classical upper bounds actually supply. Its companion `KServer.extended_cost_lemma_unordered` asks for the growth bound at *every* configuration, including degenerate ones in which two servers share a point. Those configurations have no counterpart in the classical theory, where a configuration is a set of $k$ points, and their increments genuinely misbehave: on a metric space of $k+1$ points the maximum of $\widehat w_t(X)-\widehat w_{t-1}(X)$ over all configurations can exceed its maximum over the injective ones at individual steps. Restricting the hypothesis to injective configurations removes that gap and makes the classical arguments directly applicable.
--
--   **Why the algorithm may be kept injective.** The Work Function Algorithm moves, at each step, to a configuration covering $r_t$ that almost minimises $\widehat w_{t-1}(Y)+d(C_{t-1},Y)$. By `KServer.moveCost_injective_between`, whenever the current configuration $C_{t-1}$ is injective every competitor $Y$ can be replaced by an injective one lying between $Y$ and $C_{t-1}$, which by the Lipschitz property of the work function is at least as good. So started at $X_0$ the algorithm stays injective forever, and the growth bound is only ever consulted at injective configurations.
--
--   **Formalization Note** The algorithm starts at the injective $X_0$ rather than at $C_0$, and its first move is corrected by the triangle inequality; the correction is $d(C_0,X_0)$, a constant, so the additive constant comes out as $c+1+2\,d(C_0,X_0)$ — the extra $1$ being the total slack of the approximate minimisation, which uses error $2^{-t}$ at step $t$ because on a general metric space the minimiser need not exist. No finiteness or compactness hypothesis on $M$ is needed; the hypothesis that some injective configuration exists is what replaces $k\le|M|$.
-- source:
--   E. Koutsoupias, The k-server problem (survey), Computer Science Review 3 (2009) 105-118, https://doi.org/10.1016/j.cosrev.2009.04.002, Section 3.4, Lemma 2 (Extended Cost Lemma) together with equation (7); originally M. Chrobak, L. Larmore, The server problem and on-line games, in: On-line Algorithms, DIMACS Series in Discrete Mathematics and Theoretical Computer Science 7 (1992) 11-64.

import Mathlib
import Definitions.Def_KServer_workfunctionU

namespace KServer

theorem extended_cost_lemma_injective (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (C₀ X₀ : Config k M) (hX₀ : Function.Injective X₀) (lam c : ℝ)
    (H : ∀ σ : List M, ∃ u : ℕ → ℝ,
      (∀ t : ℕ, t < σ.length → ∀ X : Config k M, Function.Injective X →
          workFnU C₀ (σ.take (t + 1)) X ≤ workFnU C₀ (σ.take t) X + u t) ∧
      (∑ t ∈ Finset.range σ.length, u t) ≤ lam * offlineCost C₀ σ + c) :
    ∃ A : OnlineAlgorithm k M, A.conf [] = C₀ ∧ IsCompetitive A (lam - 1) := by sorry

end KServer
