-- Prove2me | Theorems.Thm_InfoShareH2_proposition_4
-- name    : InfoShareH2.proposition_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:30:07.066345+00:00
-- url     : https://prove2.me/theorems/9bbbd141-40a2-4a8a-89d3-ca26c15435ea
-- title:
--   Proposition 4 — outer $\iff$ $c\cdot$Szegő function $\iff$ invertible orders
-- statement:
--   1. For every $\tilde\psi\in H^2$ the following are equivalent: (a) $\tilde\psi$ is outer; (b) there is a constant $c$ with $|c|=1$ such that $\tilde\psi(z)=c\,Q(z)$ for $|z|<1$, where $Q$ is the Szegő function
--   $$Q(z)=\exp\Bigl(\frac1{2\pi}\int_{-\pi}^{\pi}\frac{e^{i\lambda}+z}{e^{i\lambda}-z}\log|\tilde\psi(e^{i\lambda})|\,d\lambda\Bigr).\qquad(29)$$
--   2. For real square-summable $\tilde\psi$, (a) is equivalent to (c): on any probability space carrying a Gaussian white noise $(\epsilon_t)$ with variance $\sigma_\epsilon^2>0$, and for any $d$, the order process $O_t=d+\sum_n\tilde\psi_n\epsilon_{t-n}$ is invertible with respect to $(\epsilon_t)$, i.e. $M_O(t)=M_\epsilon(t)$ for all $t$.
--
--   The equivalence (a)⇔(c) is the dictionary between outer functions and orders from which the supplier can recover the demand shocks.
--
--   Differences from the source:
--   - reading: (c) for "the order process {O_t = d + ∑ψ̃_n ε_{t−n}}" → for real square-summable ψ̃, every probability space with Gaussian white noise of variance σ_ε² > 0 (Assumption 1(a)) and every d; reason: orders are real; σ_ε > 0 excludes the degenerate noise ε ≡ 0, for which every process is invertible
--   - encoding: (b) "Q(z) = lim_{r↑1} Q(rz)" → (b) stated on D; reason: the clause only extends Q to T
--   - encoding: linear pasts sp{1, X_t, X_{t−1}, …} → closed spans in L²(P); reason: Definition 1
-- source:
--   Caldentey–Giloni–Hurvich–Zhang, Information Design and Sharing in Supply Chains, SSRN 4319721 (v. 2024-01-20), https://ssrn.com/abstract=4319721, Proposition 4, p.23, (29) ((a)⇔(b) cited: Nikolski 2019, Thm 2.6.7; (a)⇔(c) §9.9, p.45)

import Mathlib
import Definitions.Def_InfoShareH2_Model
import Definitions.Def_InfoShareH2_Hardy
import Definitions.Def_InfoShareH2_Process

open Filter Topology MeasureTheory Complex

set_option autoImplicit false

namespace InfoShareH2

/-- **Proposition 4 (outer functions and invertible orders).**
SSRN 4319721 (v. 2024-01-20), Proposition 4, p.23 ((a)⇔(b) cited from Nikolski 2019, Thm 2.6.7;
(a)⇔(c) proved in §9.9, p.45). "Let `ψ̃(z) = ∑ ψ̃_n zⁿ` be a function in `H²`. The following
assertions are equivalent: (a) The function `ψ̃ ∈ H²_O`. (b) There exists a constant `c ∈ T` such
that `ψ̃(z) = cQ(z)`, where `Q(z) = lim_{r↑1} Q(rz)` and `Q(z)` is the Szegő maximal function (29),
`z ∈ D`. (c) The order process `{O_t = d + ∑ ψ̃_n ε_{t−n}}` with `∑ ψ̃_n² < ∞` is invertible with
respect to `{ε_t}`."

**Formalization Note** (a)⇔(b) is stated for every `ψ̃ ∈ H²` (complex coefficients), on `D`; the
clause `Q(z) = lim_{r↑1} Q(rz)` only extends `Q` to `T` and is not a further condition. (c) is about
a real order process, so (a)⇔(c) is stated for real square-summable coefficients, on every
probability space carrying a Gaussian white noise `{ε_t}` as in Assumption 1(a) with `σ_ε > 0`, and
for every mean `d`; the order process is the `L²` element (5) and invertibility is Definition 2. -/
theorem proposition_4 :
    (∀ a ∈ H2, IsOuter a ↔ ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ z ∈ Disk, zTransform a z = c * outerPart a z) ∧
    (∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (σε : ℝ),
      0 < σε → ∀ (d : ℝ) (ε : ℤ → Ω → ℝ), IsGaussianWhiteNoise P σε ε →
      ∀ ψ : ℕ → ℝ, Summable (fun n => ψ n ^ 2) →
        (IsOuter (ofRealSeq ψ) ↔ IsInvertibleWRT P (orderL2 P ψ d ε) ε)) := by sorry

end InfoShareH2
