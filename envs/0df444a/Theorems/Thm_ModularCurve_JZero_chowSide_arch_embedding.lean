-- Prove2me | Theorems.Thm_ModularCurve_JZero_chowSide_arch_embedding
-- name    : ModularCurve.JZero.chowSide_arch_embedding
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:41.339792+00:00
-- url     : https://prove2.me/theorems/ffe71174-e446-57b3-ac78-dc05da19cc4b
-- title:
--   Archimedean Chow-side estimate for embedding sections on X₀(N)
-- statement:
--   Fix $N \ge 1$ and let $\bar F_N$ denote `modularFunctionFieldBar N`, the base change to $\overline{\mathbb{Q}}$ of the full modular function field of level $N$ inside Laurent series, with distinguished place $\bar\infty =$ `cuspInftyBar N` and embedding divisor $E =$ `embDivisor N` $= (\mathrm{embDegree}\,N)\cdot[\bar\infty]$. Let $s : \mathrm{Fin}\,r \to \bar F_N$ satisfy `IsEmbBasis N s`, i.e. $s$ is linearly independent over $\overline{\mathbb{Q}}$ and spans the Riemann–Roch space $L(E) = \{f : v(f) \le \exp(E v)\ \text{for all places } v\}$, and let $t \in \bar F_N$ have $\operatorname{ord}_{\bar\infty} t = 1$. Then there is a real $c$ such that for every ring homomorphism $\sigma : \overline{\mathbb{Q}} \to \mathbb{C}$, every $k \in \mathbb{N}$, every nonzero $u \in L(kE)$ and every divisor $B$ with $B w = \operatorname{ord}_w u + k\,E w$ for all places $w$, provided the Chow-form reciprocity identity `ChowReciprocity s (embDivisor N) k' u' B'` holds for all $k'$, all nonzero $u' \in L(k'E)$ and all divisors $B'$ of the same shape, there exists $m \in \mathbb{R}$ satisfying two estimates with the single constant $c$ and the single $m$: first, at the cusp, with $B$ stripped of its value at $\bar\infty$, $$\bigl|\,\mathrm{chowSide}(\|\sigma(\cdot)\|, s, B.\mathrm{erase}\,\bar\infty, \bar\infty) - \bigl(k\log \sup_i \|\sigma(\mathrm{evalVec}\,s\,\bar\infty\,i)\| - \log\|\sigma(\mathrm{regVal}\,s\,\bar\infty\,t\,k\,(B\bar\infty)^{+}\,u)\| - m\bigr)\,\bigr| \le c\,k,$$ and second, for every place $v$ with $B v = 0$, the same inequality with $B$, $v$, and $\log\|\sigma(\mathrm{secVal}\,s\,v\,k\,u)\|$ in place of the erased divisor, the cusp and the regularised value. Here $\mathrm{chowSide}$ of a divisor $Z$ at $v$ is $\sum_w Z_w \log \sup_i \|\sigma(\mathrm{evalVec}\,s\,w\,i)\|$ minus the local Chow-form quantity `chowLogAt` of $Z$ at $v$, $\mathrm{evalVec}\,s\,w$ is the vector of residues at $w$ of the $s_i$ normalised by the pivot coordinate $s(\mathrm{pivotIndex}\,s\,w)$, $\mathrm{secVal}\,s\,v\,k\,u$ is the residue at $v$ of $u\,s(\mathrm{pivotIndex}\,s\,v)^{-k}$, and $\mathrm{regVal}\,s\,\bar\infty\,t\,k\,e\,u$ is the residue at $\bar\infty$ of $u\,s(\mathrm{pivotIndex}\,s\,\bar\infty)^{-k}\,t^{-e}$ (all taken as $0$ when $r = 0$).
--
--   This is the archimedean local comparison between the Chow side of the zero-cycle $B = \operatorname{div}(u) + kE$ of a section $u$ of $L(kE)$ and the naive local expression $k\log\|x_v\| - \log|u(v)| - m$, uniformly in $\sigma$, $k$ and $u$, with an error $O(k)$ and one normalising constant $m$ valid simultaneously at the base cusp and away from the support of $B$. It is the analytic input to [`ModularCurve.JZero.jensen_arch_embedding`](thm.html#ModularCurve.JZero.jensen_arch_embedding), on the way to quadraticity of the naive height on $J_0(N)$ computed through Chow forms of hyperplane-section pencils.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JZero_chowSide_arch_embedding.lean

import Definitions.Def_ModularCurve_JZeroHeightForm
import Definitions.Def_AlgebraicCurve_ChordalProximity
import Definitions.Def_AlgebraicCurve_CycleChowForm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem ModularCurve.JZero.chowSide_arch_embedding (N : ℕ) [NeZero N] {r : ℕ}
    (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s)
    (t : modularFunctionFieldBar N) (ht : (cuspInftyBar N).ord t = 1) :
    ∃ c : ℝ, ∀ (σ : (AlgebraicClosure ℚ) →+* ℂ) (k : ℕ) (u : modularFunctionFieldBar N), u ≠ 0 →
      u ∈ riemannRochSpace ((k : ℤ) • embDivisor N) →
      ∀ B : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      (∀ w, B w = w.ord u + ((k : ℤ) • embDivisor N) w) →
      (∀ (k' : ℕ) (u' : modularFunctionFieldBar N)
          (B' : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)),
          u' ≠ 0 → u' ∈ riemannRochSpace ((k' : ℤ) • embDivisor N) →
          (∀ w, B' w = w.ord u' + ((k' : ℤ) • embDivisor N) w) →
          ChowReciprocity s (embDivisor N) k' u' B') →
      ∃ m : ℝ,
        |chowSide (fun a => ‖σ a‖) s (B.erase (cuspInftyBar N)) (cuspInftyBar N)
            - ((k : ℝ) * Real.log (⨆ i, ‖σ (evalVec s (cuspInftyBar N) i)‖)
                - Real.log ‖σ (regVal s (cuspInftyBar N) t k (B (cuspInftyBar N)).toNat u)‖ - m)|
          ≤ c * k ∧
        ∀ v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), B v = 0 →
          |chowSide (fun a => ‖σ a‖) s B v
              - ((k : ℝ) * Real.log (⨆ i, ‖σ (evalVec s v i)‖)
                  - Real.log ‖σ (secVal s v k u)‖ - m)|
            ≤ c * k := by sorry
