-- Prove2me | Theorems.Thm_OptRobustCD_lemma_5_3
-- name    : OptRobustCD.lemma_5_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T23:52:04.171212+00:00
-- url     : https://prove2.me/theorems/86798e85-368c-48d9-b0cf-2715c0dfa4e4
-- title:
--   Lemma 5.3 — robust postprocessing: from $y\approx\pm\sigma^{(s)}/\|\sigma^{(s)}\|$ and a corrupted $F$, linear time gives $\min_a\|\hat\xi(F)-a\xi\|\le\varepsilon$
-- statement:
--   Let $(G,\sigma^\star)\sim\mathrm{SBM}(n,d,\lambda)$ and let $\xi$ be a unit eigenvector of $B_G$ for its eigenvalue of second-largest modulus. For every $d\ge1$, $\lambda\in(-1,1)$ with $d\lambda^2>1$ and $\varepsilon>0$ there are $\eta>0$, $\delta>0$, $s_0\in\mathbb N$ and a linear-time algorithm with the following guarantee for every $s\ge s_0$: with high probability over $(G,\sigma^\star)$, given input $y\in\mathbb R^n$ with
--   $$\min_{a\in\{\pm1\}}\Bigl\|y-a\frac{\sigma^{(s)}}{\|\sigma^{(s)}\|}\Bigr\|\le\delta$$
--   and an arbitrary graph $F$ with $|E(F)\triangle E(G)|\le\eta n$, the algorithm outputs a vector $\hat\xi(F)$ with
--   $$\min_{a\in\{\pm1\}}\|\hat\xi(F)-a\xi\|\le\varepsilon.$$
--
--   It is the last step of the algorithm of Theorem 5.1.
--
--   Differences from the source:
--   - reading: a linear-time algorithm → one real-RAM program (no oracle) halting within C(n + |E(F)| + 1) steps on every input and tape, with the guarantee on every tape; reason: the paper names no machine; OptRobustCD.Machine
--   - encoding: the output ξ̂(F) ∈ R^{E⃗} → a vector on ordered pairs written as sparse triples (EVecCode); reason: a dense output would take n² steps
--   - reading: let ξ be a unit eigenvector for the eigenvalue of B_G of second-largest modulus → inside the event: such a ξ (IsInfEig) exists, and the conclusion holds for every such ξ; reason: the paper presumes the eigenvalue real and simple, which holds w.h.p.; the existence clause rules out vacuity
--   - encoding: with high probability → the SBM(n,d,λ) probability of the event tends to 1 (Whp); reason: the meaning of the phrase
--   - encoding: quotients the source writes only where they are defined → Lean's x/0 = 0 at a zero denominator; reason: changes no instance where the source's quotient is defined; on the high-probability event the denominators are nonzero
-- source:
--   Hopkins, Hua, Mohanty, Rajaraman, Steurer, Optimal Robust Community Detection, STOC 2027 submission (manuscript of November 3, 2026, sha256 3d287d5422db7c4a43e74333bda1dbed204af51a25fd9f2c6e875ae03a4dafa1), Lemma 5.3, p.25 (pdf p.27); restated p.43 (pdf p.45)

import Mathlib
import Definitions.Def_OptRobustCD_Whp
import Definitions.Def_OptRobustCD_NBMatrix
import Definitions.Def_OptRobustCD_nbWalks
import Definitions.Def_OptRobustCD_Layouts

namespace OptRobustCD

/-- **Lemma 5.3** (Robust postprocessing). Hopkins, Hua, Mohanty, Rajaraman, Steurer, *Optimal
Robust Community Detection*, STOC 2027 submission (manuscript of November 3, 2026, sha256
3d287d54…), Lemma 5.3, p.25 (pdf p.27; restated p.43, pdf p.45).

"Let (G, σ⋆) ∼ SBM(n, d, λ) and ξ be a unit eigenvector for the eigenvalue of `B_G` of
second-largest modulus. For every d ⩾ 1, λ ∈ (−1, 1) with dλ² > 1, and ε > 0, there are η > 0,
δ > 0, `s_0 ∈ N`, and a linear-time algorithm with the following guarantee for every `s ⩾ s_0`: with
high probability over (G, σ⋆), given input `y ∈ R^n` satisfying
`min_{a∈{±1}} ∥y − a σ^{(s)}/∥σ^{(s)}∥∥ ⩽ δ`, and an arbitrary graph F satisfying
|E(F)△E(G)| ⩽ ηn, the algorithm outputs a vector `ξ̂(F)` such that `min_{a∈{±1}} ∥ξ̂(F) − aξ∥ ⩽ ε`."

**Formalization Note.**
* The algorithm is one program `P` of the real RAM (`Machine`, no oracle), chosen with `η, δ, s₀`
  and before `s` and `n`. Its input is a code of `F` followed by `y₀, …, y_{n−1}`; on every such
  input and every tape it halts within `C(n + |E(F)| + 1)` steps (linear time) and outputs a
  vector on ordered pairs as sparse triples (`EVecCode`).
* The guarantee is required on every tape. The event asserts that an informative eigenvector
  exists and quantifies over all of them, then over `y`, `F` and the encoding of `F`. -/
theorem lemma_5_3 (d lam : ℝ) (hd : 1 ≤ d) (hlam : lam ∈ Set.Ioo (-1 : ℝ) 1)
    (hKS : 1 < d * lam ^ 2) (ε : ℝ) (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∃ δ : ℝ, 0 < δ ∧ ∃ s₀ : ℕ, ∃ P : Program, NoOracle P ∧ ∃ C : ℝ,
      (∀ (n : ℕ) (F : SimpleGraph (Fin n)) (y : Fin n → ℝ) (c : List ℝ), GraphCode F c →
        HaltsWithin P noOracle (c ++ List.ofFn y) (C * ((n : ℝ) + numEdges F + 1)) ∧
        ∀ ω, ∃ z : EVec n, EVecCode z (finalOut P noOracle (c ++ List.ofFn y) ω)) ∧
      ∀ s : ℕ, s₀ ≤ s → Whp d lam (fun n σ G =>
        (∃ ξ : EVec n, IsInfEig G ξ) ∧ ∀ ξ : EVec n, IsInfEig G ξ →
        ∀ y : Fin n → ℝ,
          min (l2 (fun i => y i - sigmaS d lam s G σ i / l2 (sigmaS d lam s G σ)))
            (l2 (fun i => y i + sigmaS d lam s G σ i / l2 (sigmaS d lam s G σ))) ≤ δ →
        ∀ F : SimpleGraph (Fin n), (editDist F G : ℝ) ≤ η * n →
        ∀ c : List ℝ, GraphCode F c → ∀ ω, ∀ z : EVec n,
          EVecCode z (finalOut P noOracle (c ++ List.ofFn y) ω) →
            min (l2 (z - ξ)) (l2 (z + ξ)) ≤ ε) := by sorry

end OptRobustCD
