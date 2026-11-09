-- Prove2me | Theorems.Thm_LinearChoresCLS_theorem_6_12
-- name    : LinearChoresCLS.theorem_6_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T21:59:48.70642+00:00
-- url     : https://prove2.me/theorems/7d3cddc5-adba-46e9-9703-c9fe4e009af2
-- title:
--   Theorem 6.12 — normalization error, remainder bound $3t^3$
-- statement:
--   Consider the market with $L$-layer gadget chains on all pairs, adjusted earning requirements (6.12) and adjusted supplies (6.19), with $L\ge1$ and $0<t<1/8$, and let $n\ge1$. For every $x\in[0,1]^n$,
--   $$
--   \Psi(\tilde p(x))=\Psi(p(x))+R_{\mathrm{norm}}(x),\qquad R_{\mathrm{norm}}(x)=(n+1)\log\frac{T(x)}{n+1}.
--   $$
--   The remainder satisfies $|R_{\mathrm{norm}}(x+he_\ell)-R_{\mathrm{norm}}(x)|\le3t^3|h|$ for every $\ell\in[n]$ and every coordinate segment from $x$ to $x+he_\ell$ in $[0,1]^n$; moreover, for every feasible coordinate direction $\tilde v\in\{\pm e_\ell\}$ at $x$, the right directional derivative exists and $|R'_{\mathrm{norm}}(x;\tilde v)|\le3t^3$.
--
--   Normalizing the full price vector to the price domain changes the objective only by a third-order term, because of the supply adjustment (6.19).
--
--   **Formalization Note** $\Psi$ is the generic objective of the market at the price families $p$ and $\tilde p=\frac{n+1}{T}p$.
--
--   Differences from the source:
--   - generalization: the market of Section 6.5 with the construction's t and L (Section 7: t = 2^{−L} by (7.1)) → any integer L ≥ 1 and real 0 < t < 1/8; reason: the proof (p.50) states exactly this range ("Let L ≥ 1 and 0 < t < 1/8, as in Lemma C.1"); (7.1) is an instance
-- source:
--   Liu–Ma–Tao–Yang–Zheng, Competitive Equilibrium for Linear Chores is CLS-complete, arXiv:2611.06589 (held version, sha256 85d34a9e048d151ecff70a8614b9c2dd44307d5cf60faba74d14b2dd7eedc0b5), Theorem 6.12, Eq. (6.20), p.29 (proof Appendix C.3, pp.50–51)

import Mathlib
import Definitions.Def_LinearChoresCLS_Remainders
import Definitions.Def_LinearChoresCLS_RightDeriv

open Finset NetworkEquilibriumCLS.LinearNash

namespace LinearChoresCLS

/-- **Theorem 6.12 (Normalization error)** (arXiv:2611.06589, held version sha256 85d34a9e…,
p.29; proof pp.50–51). For the market with `L`-layer gadget chains, adjusted earning requirements
(6.12) and adjusted supplies (6.19), with `L ≥ 1` and `0 < t < 1/8`, and every `x ∈ [0,1]ⁿ`:
`Ψ(p̃(x)) = Ψ(p(x)) + R_norm(x)`, where `p̃ = ((n+1)/T) p` and `R_norm = (n+1) log(T/(n+1))`; the
remainder satisfies `|R_norm(x + he_ℓ) − R_norm(x)| ≤ 3t³|h|` for every `ℓ ∈ [n]` and every
coordinate segment from `x` to `x + he_ℓ` in `[0,1]ⁿ`; and for every feasible coordinate direction
`ṽ ∈ {±e_ℓ}` at `x` the right directional derivative exists and `|R′_norm(x; ṽ)| ≤ 3t³`.

**Formalization Note.** `Ψ` is the generic logarithmic objective of `chainMarket P t L`. The range
`L ≥ 1`, `0 < t < 1/8` is the one stated in the proof (p.50, "as in Lemma C.1"); the completed
market of (7.1) is the instance `t = 2^{−L}`, `L ≥ 8`. -/
theorem theorem_6_12 {n : ℕ} (hn : 0 < n) (P : Quadratic n) (t : ℝ) (L : ℕ) (hL : 1 ≤ L)
    (ht : 0 < t) (ht8 : t < 1 / 8) :
    (∀ x : Fin n → ℝ, InCube x →
      (chainMarket P t L).Psi (normPrice P t L x) =
        (chainMarket P t L).Psi (priceFam t L x) + Rnorm P t L x) ∧
    (∀ (x : Fin n → ℝ) (ℓ : Fin n) (h : ℝ), InCube x → InCube (x + h • Pi.single ℓ (1 : ℝ)) →
      |Rnorm P t L (x + h • Pi.single ℓ (1 : ℝ)) - Rnorm P t L x| ≤ 3 * t ^ 3 * |h|) ∧
    (∀ (x : Fin n → ℝ) (ℓ : Fin n) (s : Bool), InCube x → FeasibleCoordDir x ℓ s →
      ∃ D : ℝ, HasRightDerivAt0 (fun h => Rnorm P t L (x + h • coordDir ℓ s)) D ∧
        |D| ≤ 3 * t ^ 3) := by sorry

end LinearChoresCLS
