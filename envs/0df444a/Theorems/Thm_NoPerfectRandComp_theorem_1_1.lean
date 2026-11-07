-- Prove2me | Theorems.Thm_NoPerfectRandComp_theorem_1_1
-- name    : NoPerfectRandComp.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:45:57.631319+00:00
-- url     : https://prove2.me/theorems/a901b449-c77d-4af7-bb6f-80140abc0d96
-- title:
--   Theorem 1.1 — no total–total randomized composition, $\mathrm{R}(f\circ g)=\Theta(\mathrm{R}(f)\mathrm{R}(g)/\log\mathrm{R}(g))$
-- statement:
--   There are families of nonconstant total Boolean functions $f$ on $N$ variables and $g$ on $n$ variables with
--   $$
--   \mathrm{R}(f) = \Theta\big(N^{2/3}(\log N)^{3/4}(\log\log N)^{1/3}\big), \qquad \mathrm{R}(g) = \Theta(n^{4/5}\log n).
--   $$
--   The families can be coupled with outer size $N = 2^{\Theta(n^{4/5})}$. Their block composition has input length $L = N\cdot n = \Theta\big(N(\log N)^{5/4}\big)$ and satisfies
--   $$
--   \frac{\mathrm{R}(f\circ g)}{\mathrm{R}(f)\,\mathrm{R}(g)} = \Theta\Big(\frac1{\log n}\Big) = \Theta\Big(\frac1{\log\log L}\Big) = o(1).
--   $$
--   The saving relative to the product, $\mathrm{R}(f)\mathrm{R}(g)/\mathrm{R}(f\circ g)$, is $\Theta(\log \mathrm{R}(g))$. Here $\log = \log_2$.
--
--   This answers negatively whether $\mathrm{R}(f\circ g) \ge c\,\mathrm{R}(f)\mathrm{R}(g)$ holds with a universal $c > 0$ for total Boolean functions.
--
--   **Formalization Note** The families are indexed by $s \in \mathbb N$; every $\Theta$ and the $o(1)$ are along $s \to \infty$. $N = 2^{\Theta(n^{4/5})}$ is stated as $\log_2 N = \Theta(n^{4/5})$, and $L = N\cdot n$ is the number of coordinates of $f\circ g$. All exponents are real numbers.
--
--   Differences from the source:
--   - reading: "families of functions" with asymptotic statements → sequences indexed by s ∈ ℕ, every Θ and o(1) as s → ∞; reason: the families of the proof are indexed by s (q = 2^s − 1)
--   - encoding: N = 2^{Θ(n^{4/5})} → log₂ N = Θ(n^{4/5}); reason: the same statement
-- source:
--   Meiburg, No Perfect Randomized Composition, arXiv:2610.31638 (held version, sha256 5122a74a…), Theorem 1.1, pp.1–2 (proof §5, pp.26–27)

import Mathlib
import Definitions.Def_OAI_Combinatorics_Sensitivity_Composition
import Definitions.Def_NoPerfectRandComp_Reps
import Definitions.Def_NoPerfectRandComp_IsNonconst
open Asymptotics Filter Topology

namespace NoPerfectRandComp

/-- Theorem 1.1 of Meiburg, *No Perfect Randomized Composition*, arXiv:2610.31638 (held version, sha256 5122a74a…aeae3), pp.1–2 (no total–total randomized composition): there are families of
nonconstant total Boolean functions `f` on `N` variables and `g` on `n` variables with
`R(f) = Θ(N^{2/3} (log N)^{3/4} (log log N)^{1/3})` and `R(g) = Θ(n^{4/5} log n)`, coupled
with `N = 2^{Θ(n^{4/5})}`; their block composition has input length
`L = N · n = Θ(N (log N)^{5/4})` and satisfies
`R(f ∘ g) / (R(f) R(g)) = Θ(1/log n) = Θ(1/log log L) = o(1)`; the saving relative to the
product is `Θ(log R(g))`.

**Formalization Note** The families are indexed by `s ∈ ℕ` and every `Θ` and `o(1)` is along
`s → ∞` (`Asymptotics.IsTheta` and `Filter.Tendsto` at `atTop`). `log` is `Real.logb 2`, and all
exponents are real. `N = 2^{Θ(n^{4/5})}` is `log₂ N = Θ(n^{4/5})`. The composition `f ∘ g` is
`OAI.Paper320.compose`, on `Fin N × Fin n`, so `L = N · n`. The saving is
`R(f) R(g) / R(f ∘ g)`. -/
theorem theorem_1_1 :
    ∃ (N n : ℕ → ℕ) (f : ∀ s, (Fin (N s) → Bool) → Bool) (g : ∀ s, (Fin (n s) → Bool) → Bool),
      (∀ s, IsNonconst (f s) ∧ IsNonconst (g s)) ∧
      (fun s => (Rt (f s) : ℝ)) =Θ[atTop]
        (fun s => (N s : ℝ) ^ (2 / 3 : ℝ) * Real.logb 2 (N s) ^ (3 / 4 : ℝ) *
          Real.logb 2 (Real.logb 2 (N s)) ^ (1 / 3 : ℝ)) ∧
      (fun s => (Rt (g s) : ℝ)) =Θ[atTop]
        (fun s => (n s : ℝ) ^ (4 / 5 : ℝ) * Real.logb 2 (n s)) ∧
      (fun s => Real.logb 2 (N s)) =Θ[atTop] (fun s => (n s : ℝ) ^ (4 / 5 : ℝ)) ∧
      (fun s => (N s : ℝ) * n s) =Θ[atTop]
        (fun s => (N s : ℝ) * Real.logb 2 (N s) ^ (5 / 4 : ℝ)) ∧
      (fun s => (Rt (OAI.Paper320.compose (f s) (g s)) : ℝ) / ((Rt (f s) : ℝ) * Rt (g s)))
        =Θ[atTop] (fun s => 1 / Real.logb 2 (n s)) ∧
      (fun s => (Rt (OAI.Paper320.compose (f s) (g s)) : ℝ) / ((Rt (f s) : ℝ) * Rt (g s)))
        =Θ[atTop] (fun s => 1 / Real.logb 2 (Real.logb 2 ((N s : ℝ) * n s))) ∧
      Tendsto
        (fun s => (Rt (OAI.Paper320.compose (f s) (g s)) : ℝ) / ((Rt (f s) : ℝ) * Rt (g s)))
        atTop (𝓝 0) ∧
      (fun s => (Rt (f s) : ℝ) * Rt (g s) / Rt (OAI.Paper320.compose (f s) (g s)))
        =Θ[atTop] (fun s => Real.logb 2 (Rt (g s))) := by sorry

end NoPerfectRandComp
