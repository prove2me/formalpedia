-- Prove2me | Theorems.Thm_ModularCurve_JZero_jensen_arch_embedding
-- name    : ModularCurve.JZero.jensen_arch_embedding
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:41.339792+00:00
-- url     : https://prove2.me/theorems/4668276b-1c44-5162-b9ec-eb4f929e36cc
-- title:
--   Archimedean Jensen comparison at all complex embeddings
-- statement:
--   Fix a level $N \ge 1$ and work in $F =$ `modularFunctionFieldBar N`, the base change to $\overline{\mathbb{Q}}$ of the full modular function field of level $N$, realised inside Laurent series over $\overline{\mathbb{Q}}$. Let $s : \mathrm{Fin}\,r \to F$ satisfy `IsEmbBasis N s`, i.e. $s$ is linearly independent over $\overline{\mathbb{Q}}$ and its span is the Riemann–Roch space $L(D)$ of $D =$ `embDivisor N` $= (\mathrm{embDegree}\,N)\cdot[\infty]$, the indicated multiple of the cusp `cuspInftyBar N`; here $L(D) = \{f : v(f) \le \exp(D v) \text{ for all places } v\}$ for the adic valuations of places of $F$ over $\overline{\mathbb{Q}}$. Let $t \in F$ have order $1$ at the cusp. The assertion is that there is a constant $c \in \mathbb{R}$ such that for every ring homomorphism $\sigma : \overline{\mathbb{Q}} \to \mathbb{C}$, every $k \in \mathbb{N}$, every nonzero $u \in L(kD)$ and every divisor $B$ with $B w = \mathrm{ord}_w(u) + k\,D(w)$ at all places $w$, there is $m \in \mathbb{R}$ with two inequalities, the absolute value being $a \mapsto \lVert \sigma a\rVert$. First, the sum over $w$ in the support of $B$ with the cusp term erased of $B(w)$ times the chordal proximity $\mathrm{prox}$ between the normalised coordinate vectors `evalVec s` at the cusp and at $w$ differs from $k \log \sup_i \lVert \sigma(\mathrm{evalVec}\,s\,\infty\,i)\rVert - \log \lVert \sigma(\mathrm{regVal}\,s\,\infty\,t\,k\,(B\infty)^{+}\,u)\rVert - m$ by at most $c k$, where `regVal` evaluates $u \cdot s(\text{pivot})^{-k} t^{-(B\infty)^{+}}$ at the cusp. Second, for every place $v$ with $B v = 0$, the full $B$-weighted proximity sum based at $v$ differs from $k \log \sup_i \lVert \sigma(\mathrm{evalVec}\,s\,v\,i)\rVert - \log \lVert \sigma(\mathrm{secVal}\,s\,v\,k\,u)\rVert - m$ by at most $c k$, where `secVal` evaluates $u \cdot s(\text{pivot})^{-k}$ at $v$. Here $\mathrm{prox}(\nu, x, y) = \log\sup_i \nu(x_i) + \log\sup_i \nu(y_i) - \log \sup_{i,j} \nu(x_i y_j - x_j y_i)$.
--
--   This is the archimedean half of the height comparison used for the Jacobian $J_0(N)$, a Jensen/Mahler-measure estimate: the proximity sum of a section's divisor to a base point is compared, with error linear in the degree $k$, with the logarithm of a normalised value of the section. The number-field-free formulation over arbitrary embeddings $\sigma$ feeds [`ModularCurve.JZero.jensen_arch`](thm.html#ModularCurve.JZero.jensen_arch), [`ModularCurve.JZero.jensen_arch_at_of_nonCuspidal`](thm.html#ModularCurve.JZero.jensen_arch_at_of_nonCuspidal) and [`ModularCurve.JZero.prox_sum_le_of_forall_log_secVal_le`](thm.html#ModularCurve.JZero.prox_sum_le_of_forall_log_secVal_le).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JZero_jensen_arch_embedding.lean

import Definitions.Def_ModularCurve_JZeroHeightForm
import Definitions.Def_AlgebraicCurve_ChordalProximity

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem ModularCurve.JZero.jensen_arch_embedding (N : ℕ) [NeZero N] {r : ℕ}
    (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s)
    (t : modularFunctionFieldBar N) (ht : (cuspInftyBar N).ord t = 1) :
    ∃ c : ℝ, ∀ (σ : (AlgebraicClosure ℚ) →+* ℂ) (k : ℕ) (u : modularFunctionFieldBar N), u ≠ 0 →
      u ∈ riemannRochSpace ((k : ℤ) • embDivisor N) →
      ∀ B : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      (∀ w, B w = w.ord u + ((k : ℤ) • embDivisor N) w) →
      ∃ m : ℝ,
        |((B.erase (cuspInftyBar N)).sum fun w n => (n : ℝ) *
            prox (fun a => ‖σ a‖) (evalVec s (cuspInftyBar N)) (evalVec s w))
            - ((k : ℝ) * Real.log (⨆ i, ‖σ (evalVec s (cuspInftyBar N) i)‖)
                - Real.log ‖σ (regVal s (cuspInftyBar N) t k (B (cuspInftyBar N)).toNat u)‖ - m)|
          ≤ c * k ∧
        ∀ v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), B v = 0 →
          |(B.sum fun w n => (n : ℝ) * prox (fun a => ‖σ a‖) (evalVec s v) (evalVec s w))
              - ((k : ℝ) * Real.log (⨆ i, ‖σ (evalVec s v i)‖)
                  - Real.log ‖σ (secVal s v k u)‖ - m)|
            ≤ c * k := by sorry
