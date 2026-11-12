-- Prove2me | Theorems.Thm_NetUnrelEst_Main_lemma_2_4
-- name    : NetUnrelEst.Main.lemma_2_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T07:15:35.759763+00:00
-- url     : https://prove2.me/theorems/208bd183-f4c7-42fe-b322-93d5d8b243b8
-- title:
--   Lemma 2.4 — decay of F(t) = E(K_t − 1) under contraction
-- statement:
--   Let $G$ be a connected multigraph with $n\ge2$ vertices and failure probabilities $0<p_e<1$, and let $K_t$ be the number of components of $(V,\{e:T_e\le t\})$ for independent exponential arrival times $T_e$ of rate $w_e=-\log p_e$. Put $F(t)=\mathbb E(K_t-1)$, $\zeta=-2\log(1-u)$ and $\lambda$ the minimum cut. If $u\le 2/3$, then $\zeta\le\log 9$ and, for $0\le\tau\le\tau+t\le1$,
--   $$F(\tau+t)\le F(\tau)e^{-\lambda t/2},\tag{10}$$
--   $$F(\tau+t)\le \zeta\,\big(F(\tau)/\zeta\big)^{e^{-t/2}}.\tag{11}$$
--   Inequality (11) also holds with $\zeta$ replaced by $\log 9$.
--
--   The lemma controls how fast random contraction shrinks the graph: (10) gives exponential decay at rate $\lambda/2$, and (11) a doubly exponential decay that matters when $\lambda$ is small. The algorithm's contraction times are chosen from these bounds.
--
--   **Formalization Note.** At a fixed time $t$, the arrived edges have the law of the working edges when $e$ fails with probability $p_e^t$, so $F(t)$ is a finite sum over failure sets. Since $0<p_e<1$, $u>0$, so $\zeta>0$; powers are real powers.
--
--   Differences from the source:
--   - generalization: the graph of §2.4 (the reduced graph G of §2.1, 0 < p_e < 1) → any connected multigraph on Fin n with n ≥ 2 (self-loops and parallel edges allowed); reason: loops cross no cut and parallel edges combine into one edge with the product failure probability (§2.1), so every quantity of the statement is that of the reduced graph; the reduced graph is one instance
--   - encoding: K_t for independent exponential arrival times of rate −log p_e → the number of components of the working graph when edge e fails with probability p_e^t; reason: at a fixed time the arrived set has exactly this law, and (10)–(11) concern F at fixed times
-- source:
--   Sun, Near-Linear Estimation of Network Unreliability, STOC 2027 submission, doi:10.5281/zenodo.23913531 (PDF sha256 eee2585a…), p. 11, Lemma 2.4

import Mathlib
import Definitions.Def_NetUnrelDesign_Main_Model
import Definitions.Def_NetUnrelEst_Main_CutSums
import Definitions.Def_NetUnrelEst_Main_Contraction

open scoped BigOperators ENNReal

open NetUnrelDesign.Main

namespace NetUnrelEst.Main

/-- **Lemma 2.4.** For a connected multigraph with `n ≥ 2` vertices and `0 < p_e < 1`, if
`u ≤ 2/3` then `ζ = −2 log(1 − u) ≤ log 9` and, for `0 ≤ τ ≤ τ + t ≤ 1`,
`F(τ + t) ≤ F(τ) e^{−λt/2}` (10) and `F(τ + t) ≤ ζ (F(τ)/ζ)^{e^{−t/2}}` (11), the latter also with
`ζ` replaced by `log 9`; `F(t) = E(K_t − 1)`. Sun 2027, p. 11, Lemma 2.4. -/
theorem lemma_2_4 {n m : ℕ} (ends : Ends n m) (hn : 2 ≤ n) (hconn : IsConnectedGraph ends)
    (p : Fin m → ℝ) (hp : ∀ e, 0 < p e ∧ p e < 1) (hu : unrel ends p ≤ 2 / 3) :
    zeta (unrel ends p) ≤ Real.log 9 ∧
    ∀ τ t : ℝ, 0 ≤ τ → 0 ≤ t → τ + t ≤ 1 →
      Fcomp ends p (τ + t) ≤ Fcomp ends p τ * Real.exp (-(lam ends p * t) / 2) ∧
      Fcomp ends p (τ + t) ≤
        zeta (unrel ends p) * (Fcomp ends p τ / zeta (unrel ends p)) ^ Real.exp (-t / 2) ∧
      Fcomp ends p (τ + t) ≤ Real.log 9 * (Fcomp ends p τ / Real.log 9) ^ Real.exp (-t / 2) := by sorry

end NetUnrelEst.Main
