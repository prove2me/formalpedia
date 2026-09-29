-- Prove2me | Theorems.Thm_ModularCurve_JZero_exists_hyperplaneSection_defect_le
-- name    : ModularCurve.JZero.exists_hyperplaneSection_defect_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:41.339792+00:00
-- url     : https://prove2.me/theorems/65acfb38-e3a6-5998-8fdd-7dcac5e40dc3
-- title:
--   Auxiliary hyperplane section with bounded defect on X₀(N)
-- statement:
--   Fix $N \ge 1$ and let $\bar F_N$ denote `modularFunctionFieldBar N`, the base change to $\overline{\mathbb Q}$ of the full modular function field of level $N$ inside Laurent series. Let $E$ be `embDivisor N`, that is $(2g+1)$ times the divisor of the cusp $\bar\infty$, where $2g+1$ is `embDegree N` and $g$ is `genusFF`, the dimension of $H^1(0)$, and let $s = (s_i)_{i \in \mathrm{Fin}\,r}$ satisfy `IsEmbBasis N s`, i.e. $s$ is linearly independent over $\overline{\mathbb Q}$ and spans the Riemann–Roch space $L(E) = \{f : v(f) \le \exp(E v) \text{ for all places } v\}$. Then there is a real constant $C$, independent of all the data that follow, such that for every ring embedding $\sigma : \overline{\mathbb Q} \to \mathbb C$, every finite set $S$ of places of $\bar F_N$ over $\overline{\mathbb Q}$, all coefficient vectors $a, a' : \mathrm{Fin}\,r \to \overline{\mathbb Q}$ and all divisors (finitely supported $\mathbb Z$-valued functions on places) $Z_a, Z_{a'}$ with $\sum_i a_i s_i \ne 0$, $\sum_i a'_i s_i \ne 0$ and $Z_a(w) = \mathrm{ord}_w(\sum_i a_i s_i) + E(w)$, $Z_{a'}(w) = \mathrm{ord}_w(\sum_i a'_i s_i) + E(w)$ for every place $w$, there exist $e : \mathrm{Fin}\,r \to \overline{\mathbb Q}$ and a divisor $Z_e$ such that $\sum_i e_i s_i \ne 0$, $Z_e(w) = \mathrm{ord}_w(\sum_i e_i s_i) + E(w)$ for all $w$, $Z_e$ vanishes at every place of $S$, and for every place $w$ at least one of $Z_a(w), Z_e(w)$ vanishes and at least one of $Z_{a'}(w), Z_e(w)$ vanishes; moreover, writing $\|x\|_\sigma = \sup_i \|\sigma(x_i)\|$, $x_w = (\mathrm{evalVec}\,s\,w\,i)_i$ for the pivot-normalised coordinate vector of a place $w$ (the function `evalVec`), and $F_Z = \prod_w (\sum_i x_{w,i} X_i)^{\max(Z(w),0)}$ for the Chow form `chowForm s Z`, both quantities $$\Bigl|\bigl[\log\|\sigma F_{Z_e}(a)\| - \textstyle\sum_z Z_e(z)\log\|x_z\|_\sigma - (2g+1)\log\|a\|_\sigma\bigr] - \bigl[\log\|\sigma F_{Z_a}(e)\| - \textstyle\sum_y Z_a(y)\log\|x_y\|_\sigma - (2g+1)\log\|e\|_\sigma\bigr]\Bigr|$$ and its analogue with $a$, $Z_a$ replaced by $a'$, $Z_{a'}$ are at most $C$.
--
--   The statement supplies an auxiliary hyperplane section of the embedding-divisor system on $X_0(N)$ which avoids a prescribed finite set of places, meets neither of two given sections, and has bounded archimedean defect against both; the bracketed expressions are the normalised Chow-form quantities whose asymmetry measures that defect. It is used in the proof of [`ModularCurve.JZero.hyperplaneSection_cocycle_bounded`](thm.html#ModularCurve.JZero.hyperplaneSection_cocycle_bounded), in the construction of the height on $J_0(N)$, namely `JZero N`, via Chow forms of hyperplane sections.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JZero_exists_hyperplaneSection_defect_le.lean

import Definitions.Def_ModularCurve_JZeroHeightForm
import Definitions.Def_AlgebraicCurve_ChordalProximity
import Definitions.Def_AlgebraicCurve_CycleChowForm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

open AlgebraicCurve ModularCurve

theorem ModularCurve.JZero.exists_hyperplaneSection_defect_le (N : ℕ) [NeZero N] {r : ℕ}
    (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s) :
    ∃ C : ℝ, ∀ (σ : (AlgebraicClosure ℚ) →+* ℂ)
      (S : Finset (Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)))
      (a a' : Fin r → AlgebraicClosure ℚ)
      (Za Za' : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)),
      linSec s a ≠ 0 → linSec s a' ≠ 0 → (∀ w, Za w = w.ord (linSec s a) + embDivisor N w) → (∀ w, Za' w = w.ord (linSec s a') + embDivisor N w) →
      ∃ (e : Fin r → AlgebraicClosure ℚ) (Ze : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)),
        linSec s e ≠ 0 ∧ (∀ w, Ze w = w.ord (linSec s e) + embDivisor N w) ∧ (∀ w ∈ S, Ze w = 0) ∧
        (∀ w, Za w = 0 ∨ Ze w = 0) ∧ (∀ w, Za' w = 0 ∨ Ze w = 0) ∧
        |((Real.log ‖σ (MvPolynomial.eval a (chowForm s Ze))‖
              - (Ze.sum fun z n => (n : ℝ) * Real.log (⨆ i, ‖σ (evalVec s z i)‖))
              - embDegree N * Real.log (⨆ i, ‖σ (a i)‖))
            - (Real.log ‖σ (MvPolynomial.eval e (chowForm s Za))‖
              - (Za.sum fun y n => (n : ℝ) * Real.log (⨆ i, ‖σ (evalVec s y i)‖))
              - embDegree N * Real.log (⨆ i, ‖σ (e i)‖)))| ≤ C ∧
        |((Real.log ‖σ (MvPolynomial.eval a' (chowForm s Ze))‖
              - (Ze.sum fun z n => (n : ℝ) * Real.log (⨆ i, ‖σ (evalVec s z i)‖))
              - embDegree N * Real.log (⨆ i, ‖σ (a' i)‖))
            - (Real.log ‖σ (MvPolynomial.eval e (chowForm s Za'))‖
              - (Za'.sum fun y n => (n : ℝ) * Real.log (⨆ i, ‖σ (evalVec s y i)‖))
              - embDegree N * Real.log (⨆ i, ‖σ (e i)‖)))| ≤ C := by sorry
