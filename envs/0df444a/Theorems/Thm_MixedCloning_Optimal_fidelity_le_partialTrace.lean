-- Prove2me | Theorems.Thm_MixedCloning_Optimal_fidelity_le_partialTrace
-- name    : MixedCloning.Optimal.fidelity_le_partialTrace
-- status  : Proved
-- author  : @dmitry
-- created : 2026-11-22T02:08:24.394186+00:00
-- url     : https://prove2.me/theorems/a9adeafc-13d4-4050-aaba-9c9bbecbbe30
-- title:
--   Data processing of fidelity under the partial trace
-- statement:
--   Let $a$ and $b$ be finite sets, let $m\ge0$, and consider $m$ registers $A_1B_1,\dots,A_mB_m$ with $A_t\cong\mathbb C^a$ and $B_t\cong\mathbb C^b$. Let $F(X,Y)=\big(\operatorname{tr}\sqrt{\sqrt X\,Y\sqrt X}\big)^2$ be the squared fidelity. For all positive semidefinite $X,Y$ on $(\mathbb C^a\otimes\mathbb C^b)^{\otimes m}$,
--
--   $$
--   F(X,Y)\ \le\ F\big(\operatorname{tr}_{B_1\cdots B_m}X,\ \operatorname{tr}_{B_1\cdots B_m}Y\big).
--   $$
--
--   This is the data-processing inequality for fidelity [Wat18, Theorem 3.27], specialized to the channel that traces out the auxiliary registers. The source uses it in the proofs of Proposition 10 (p. 16) and Proposition 25 (p. 27) to pass from purified outputs to the original registers.
--
--   **Formalization Note** The partial trace is the platform function `partialTrace m`, which keeps the register order $A_1\cdots A_m$. The inequality is stated for squared fidelity; it is equivalent to the root-fidelity form because root fidelity is nonnegative.
--
--   Differences from the source:
--   - specialization: an arbitrary channel $\Phi$ → the partial trace over $B_1,\dots,B_m$; reason: this is the instance used in the source
-- source:
--   John Watrous, The Theory of Quantum Information, Cambridge University Press, 2018, Theorem 3.27 (monotonicity of fidelity under channels), https://doi.org/10.1017/9781316848142; used as 'data processing of fidelity [Wat18, Theorem 3.27]' in Dmitry Grinko, Marco Fanizza, Thilo Scharnhorst, Jack Spilecki, Optimal cloning of mixed states, STOC 2027 submission #243 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/243.pdf, p. 16 (proof of Proposition 10) and p. 27 (proof of Proposition 25).

import Definitions.Def_MixedCloning_Optimal_Model

noncomputable section
open Matrix MeasureTheory
open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise

namespace MixedCloning.Optimal
attribute [local instance] Classical.propDecidable Classical.decEq

/-- Data processing of fidelity [Wat18, Theorem 3.27], used on PDF p.16 (and p.27), for the
partial trace over the auxiliary registers `B_1,…,B_m`. -/
theorem fidelity_le_partialTrace {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (m : ℕ)
    (X Y : Op (Word (a × b) m)) (hX : X.PosSemidef) (hY : Y.PosSemidef) :
    fidelity X Y ≤ fidelity (partialTrace m X) (partialTrace m Y) := by sorry

end MixedCloning.Optimal
