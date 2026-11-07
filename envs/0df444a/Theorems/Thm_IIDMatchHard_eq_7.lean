-- Prove2me | Theorems.Thm_IIDMatchHard_eq_7
-- name    : IIDMatchHard.eq_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T08:07:42.8392+00:00
-- url     : https://prove2.me/theorems/c7fcb4cb-12de-43d4-ae68-cbcfdd4208c7
-- title:
--   Eq. (7) — the online optimum of $I(\tilde G,\lambda)$ determines $C(G)$ up to a small error
-- statement:
--   Let $G$ be a simple **cubic** graph with $n$ vertices and $m$ edges, let $B\ge1$ be an integer, let $\tilde G$ be the blow-up of $G$ and let $\lambda>0$. Let $R=nB+2\lambda mB^2$ be the total rate of $I(\tilde G,\lambda)$. Then
--   $$\Big|\mathrm{OPT}(I(\tilde G,\lambda))-\Phi_{\tilde G}\big(B^2C(G)\big)\Big|\ \le\ \lambda mB^2\Big(24\lambda B+\frac1{\sqrt B}\Big)+\sqrt R+1,$$
--   where $\Phi_{\tilde G}$ is the affine function of Lemma 3.6 for $\tilde G$, which has $nB$ vertices and $mB^2$ edges.
--
--   The online optimum of the blown-up instance thus determines $C(G)$ up to an error of $O(\lambda B+1/\sqrt B)\,m$. This is the estimate behind the reduction.
--
--   Differences from the source:
--   - encoding: G cubic → every vertex has exactly three neighbors (neighborSet ncard = 3); reason: definition of cubic
--   - encoding: R, the total rate of I(G̃, λ) → totalRate (blowUp G B) λ, the number of vertices of G̃ plus 2λ times its number of edges; reason: definition of R (p.22: R = nB + 2λmB²)
--   - encoding: suprema over online policies → real suprema over deterministic policies; reason: §2.1: deterministic policies attain the optimum; the values are bounded
--   - encoding: e in Φ → Real.exp 1; reason: Lean convention; same quantity
-- source:
--   Teng, Yang, Computational Hardness of Online Stochastic Matching (manuscript of Nov. 3, 2026, sha256 f0193d92…), proof of Theorem 3.1, Eq. (7), p.23 (PDF p.24); also displayed on p.10

import Definitions.Def_IIDMatchHard_Adjusted

set_option autoImplicit false

namespace IIDMatchHard

/-- **Equation (7).** For a simple cubic graph `G`, every integer `B ≥ 1` and every `λ > 0`,
`|OPT(I(G̃, λ)) − Φ_G̃(B²C(G))| ≤ λmB²(24λB + 1/√B) + √R + 1`, where `R = nB + 2λmB²` is the
total rate of `I(G̃, λ)`. Teng, Yang, *Computational Hardness of Online Stochastic Matching* (manuscript of Nov. 3, 2026,
sha256 f0193d92…), proof of Theorem 3.1, Eq. (7), p.23 (PDF p.24); also displayed
on p.10.

**Formalization Note.** Cubic: every vertex has exactly three neighbors. `G̃ = blowUp G B`;
`Φ_G̃` is `Φ` of `G̃` (with `nB` vertices and `mB²` edges); `m` is the number of edges of `G`. -/
theorem eq_7 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hG : ∀ v, (G.neighborSet v).ncard = 3) (B : ℕ) (hB : 1 ≤ B) (lam : ℝ) (hlam : 0 < lam) :
    |OPT (cutInst (blowUp G B) lam) - Phi (blowUp G B) lam ((B : ℝ) ^ 2 * (maxCut G : ℝ))| ≤
      lam * (numEdges G : ℝ) * (B : ℝ) ^ 2 * (24 * lam * B + 1 / Real.sqrt B) +
        Real.sqrt (totalRate (blowUp G B) lam) + 1 := by sorry

end IIDMatchHard
