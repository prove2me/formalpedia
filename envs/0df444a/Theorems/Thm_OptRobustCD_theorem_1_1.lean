-- Prove2me | Theorems.Thm_OptRobustCD_theorem_1_1
-- name    : OptRobustCD.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T23:52:02.205925+00:00
-- url     : https://prove2.me/theorems/677bd425-be7e-42b2-9531-94a70e151ce1
-- title:
--   Theorem 1.1 — for every $d>1$, $\lambda\in[-1,1]$, $\varepsilon>0$: a nearly-linear-time algorithm with overlap $\mathrm{OPT}_{d,\lambda}-\varepsilon-o(1)$ against $\eta n$ adversarial edge edits
-- statement:
--   For every $d>1$, $\varepsilon>0$ and $\lambda\in[-1,1]$ there are $\eta>0$ and a nearly-linear time algorithm which takes a graph $G$ and returns a $\{\pm1\}$-labelling $\hat\sigma(G)$ of its vertices such that
--   $$\mathbb E_{(\sigma^\star,G)\sim\mathrm{SBM}(n,d,\lambda)}\ \min\Bigl\{\frac1n\bigl|\langle\sigma^\star,\hat\sigma(G')\rangle\bigr|\ :\ |E(G)\triangle E(G')|\le\eta n\Bigr\}\ \ge\ \mathrm{OPT}_{d,\lambda}-\varepsilon-o(1).$$
--   Here $\mathrm{SBM}(n,d,\lambda)$ draws uniform labels $\sigma^\star\in\{\pm1\}^n$ and joins each pair $\{u,v\}$ independently with probability $\frac dn(1+\lambda\sigma^\star_u\sigma^\star_v)$, the adversary may add or delete any $\eta n$ edges after seeing $(\sigma^\star,G)$, and
--   $$\mathrm{OPT}_{d,\lambda}=\lim_{n\to\infty}\sup_{\hat\sigma}\frac1n\mathbb E\,|\langle\sigma^\star,\hat\sigma(G)\rangle|$$
--   is the information-theoretically optimal overlap without corruption.
--
--   So robustness to a constant fraction of adversarial edits costs nothing in accuracy: the algorithm (nonbacktracking spectral initialization, robustified by an SDP, followed by belief propagation) matches the Bayes-optimal overlap.
--
--   Differences from the source:
--   - generalization: OPT_{d,λ} = lim_n sup_σ̂ (1/n) E|⟨σ⋆, σ̂(G)⟩| → limsup_n of the same quantity (sbmOPT); reason: limsup equals the limit when it exists, as the paper takes for granted, and is never smaller, so the Lean bound specializes to the source's
--   - encoding: sup over estimators σ̂ → sup over deterministic maps from graphs to labellings; reason: a randomized estimator's expected overlap is an average of deterministic ones
--   - reading: a nearly-linear time algorithm which takes a graph G and returns a {±1}-labeling → one real-RAM program (no oracle: arithmetic, comparisons, real constants, √, tanh, uniform draws, exact-integer indexing; no floor) halting within C·N·(log N)^k steps, N = n + |E(G′)| + 2, on every graph, encoding and tape, with output a ±1 list of length n; reason: the paper names no machine; worst case is the stronger reading of 'nearly-linear time'
--   - reading: E min{(1/n)|⟨σ⋆, σ̂(G′)⟩| : |E(G)△E(G′)| ⩽ ηn} for a randomized σ̂ → E over (σ⋆, G) of the inf over (G′, encoding of G′) of the tape expectation of the overlap; reason: the adversary sees (σ⋆, G) and the algorithm but not its future coins; it also picks the encoding, the stronger reading
--   - encoding: − o(1) → ∀ δ > 0, ∃ N₀, ∀ n ⩾ N₀, … ⩾ OPT − ε − δ; reason: the meaning of o(1) with the algorithm and η fixed before n
--   - encoding: the expectation over the algorithm's coins → the Bochner integral over the tape measure; reason: Lean's value 0 for a non-integrable integrand can only lower the left side, so it never makes the bound easier
-- source:
--   Hopkins, Hua, Mohanty, Rajaraman, Steurer, Optimal Robust Community Detection, STOC 2027 submission (manuscript of November 3, 2026, sha256 3d287d5422db7c4a43e74333bda1dbed204af51a25fd9f2c6e875ae03a4dafa1), Theorem 1.1, p.2 (pdf p.4); OPT on p.1 (pdf p.3)

import Mathlib
import Definitions.Def_OptRobustCD_sbmOPT
import Definitions.Def_OptRobustCD_Layouts

open MeasureTheory

namespace OptRobustCD

/-- **Theorem 1.1** (Main theorem). Hopkins, Hua, Mohanty, Rajaraman, Steurer, *Optimal Robust
Community Detection*, STOC 2027 submission (manuscript of November 3, 2026, sha256 3d287d54…),
Theorem 1.1, p.2 (pdf p.4).

"For every d > 1, ε > 0, and λ ∈ [−1, 1], there is η > 0 and a nearly-linear time algorithm which
takes a graph G, returns a {±1}-labeling σ̂(G) of the vertices, and satisfies
`E_{(σ⋆,G)∼SBM(n,d,λ)} min{(1/n)·|⟨σ⋆, σ̂(G′)⟩| s.t. |E(G)△E(G′)| ⩽ ηn} ⩾ OPT_{d,λ} − ε − o(1)`."

**Formalization Note.**
* `OPT_{d,λ}` is the definition on p.1 (`sbmOPT`, a `limsup` of the best expected overlap).
* The algorithm is one program `P` of the randomized real RAM (`Machine`: `+ − × /`, comparisons,
  real constants, `√`, `tanh`, uniform draws, exact-integer indexing, no oracle, no floor),
  chosen with `η` after `d, λ, ε` and before `n`.
* Time: on every graph `G′` on `[n]`, every encoding `l` of it (`GraphCode`) and every tape, `P`
  halts within `C·N·(log N)^k` steps, `N = n + |E(G′)| + 2`, and outputs a `±1` labelling.
* Accuracy: the adversary sees `(σ⋆, G)` and the algorithm (not its coins) and picks `G′` within
  `ηn` edits of `G` and its encoding; the minimum is inside the SBM expectation and the expectation
  over the tape is innermost. `−o(1)` is "for every `δ > 0`, for all large `n`".
* The full printed domain `d > 1`, `λ ∈ [−1, 1]` is kept, including `λ = ±1` and `dλ² ⩽ 1`. -/
theorem theorem_1_1 (d ε lam : ℝ) (hd : 1 < d) (hε : 0 < ε) (hlam : lam ∈ Set.Icc (-1 : ℝ) 1) :
    ∃ η : ℝ, 0 < η ∧ ∃ P : Program, NoOracle P ∧ ∃ C : ℝ, ∃ k : ℕ,
      (∀ (n : ℕ) (G' : SimpleGraph (Fin n)) (l : List ℝ), GraphCode G' l →
        HaltsWithin P noOracle l
          (C * ((n : ℝ) + numEdges G' + 2) * Real.log ((n : ℝ) + numEdges G' + 2) ^ k) ∧
        ∀ ω, IsLabelling n (finalOut P noOracle l ω)) ∧
      ∀ δ : ℝ, 0 < δ → ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
        sbmOPT d lam - ε - δ ≤ SBMThreshold.Main.sbmExp n (sbmA d lam) (sbmB d lam) (fun σ G =>
          ⨅ q : {q : SimpleGraph (Fin n) × List ℝ //
              (editDist G q.1 : ℝ) ≤ η * n ∧ GraphCode q.1 q.2},
            ∫ ω, SBMThreshold.Main.overlap σ (labelOfList n (finalOut P noOracle q.1.2 ω))
              ∂tapeMeasure) := by sorry

end OptRobustCD
