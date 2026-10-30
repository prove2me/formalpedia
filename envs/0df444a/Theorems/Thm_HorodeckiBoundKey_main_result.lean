-- Prove2me | Theorems.Thm_HorodeckiBoundKey_main_result
-- name    : HorodeckiBoundKey.main_result
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T03:16:38.461347+00:00
-- url     : https://prove2.me/theorems/fcf96741-83a4-41fd-b2ca-2c32f09718a0
-- title:
--   Main result: a PPT bound entangled state with strictly positive distillable key
-- statement:
--   Let $\varrho_s$ and $\varrho_a$ be the extreme Werner states (9) on $\mathbb C^d\otimes\mathbb C^d$, $\tau_0 = \varrho_s^{\otimes l}$ and $\tau_1 = [(\varrho_a+\varrho_s)/2]^{\otimes l}$ the hiding states (10), and $\rho = \rho(p,d,l)$ the state (11) on key qubits $A,B$ and shields $A' = B' = (\mathbb C^d)^{\otimes l}$: in the basis $|00\rangle,|01\rangle,|10\rangle,|11\rangle$ of $AB$,
--   $$
--   \rho = \begin{bmatrix}
--   \frac p2(\tau_0+\tau_1) & 0 & 0 & \frac p2(\tau_1-\tau_0)\\
--   0 & (\frac12-p)\tau_0 & 0 & 0\\
--   0 & 0 & (\frac12-p)\tau_0 & 0\\
--   \frac p2(\tau_1-\tau_0) & 0 & 0 & \frac p2(\tau_0+\tau_1)
--   \end{bmatrix}.
--   $$
--   For every real $p$ with $\frac14<p\le\frac13$ there are integers $l\ge 1$ and $d\ge 2$ such that, across the cut $AA':BB'$,
--   1. $\rho$ is a state;
--   2. $\rho$ has positive partial transpose;
--   3. $\rho$ is not separable;
--   4. $E_D(\rho) = 0$;
--   5. $K_D(\rho) > 0$.
--
--   Clauses 1–4 say that $\rho$ is bound entangled (p.1: "states which require entanglement to create, but from which no pure entanglement can be distilled"), and clause 5 that a secure key can nevertheless be distilled from it. This overturns the expectation that key distillation from a quantum state is possible exactly when entanglement distillation is.
--
--   **Formalization Note** $\rho$ is the published `Dependency50.P24.hidingFamily p d l` ($\tau_0$ = `hidingTwo`, $\tau_1$ = `hidingOne`); PPT is `transposeBob`, the transpose of $B$ and $B'$ together. The rates are the published operational `Gap48.P42.bipartiteDistillable` ($E_D$) and `Gap48.P42.distillableKey` ($K_\gamma$), valued in $[0,\infty]$, on the cut `finCut`.
--
--   Differences from the source:
--   - reading: distillable key K_D (key drawn by local operations and public communication; not defined formally in the paper) → K_γ, the operational private-dit rate Gap48.P42.distillableKey under deterministic finite adaptive LOCC (ℝ≥0∞); reason: p.2 identifies the two rates ("We thus have equality of the two rates", with "Clearly K_γ ≤ K_D") and the proof on p.3 distils γ states "at the same rate as K_D"; the mission uses this one key rate throughout
--   - reading: "a bound entangled state which can be shown to have K_D > 0" (no parameters named) → for every p with 1/4 < p ≤ 1/3 there are l ≥ 1 and d ≥ 2 such that ρ(p,d,l) is a PPT, non-separable state with E_D = 0 and K > 0; reason: the paragraph derives exactly this range (p ≤ 1/3 for PPT, p > 1/4 for (13) → 1/2) and chooses l, then d; the family form implies the single-state claim
--   - reading: "bound entangled" → state ∧ PPT ∧ not separable ∧ E_D = 0; reason: p.1 defines bound entangled states as states which require entanglement to create (not separable) and from which no pure entanglement can be distilled (E_D = 0); PPT is the property the paper derives for them ("PPT … being therefore bound entangled")
--   - encoding: the Alice:Bob cut AA′:BB′ of a state on A B A′ B′ → finCut: partyCut followed by a fixed relabelling of Alice's register Fin 2 × A′ as Fin (2|A′|) and Bob's likewise; reason: the published rates take matrices on Fin a × Fin b; rates, separability and partial transposition are invariant under local relabellings
--   - encoding: real-valued rates E_D and K_D → ℝ≥0∞-valued suprema; reason: avoids the junk value of a real supremum of an unbounded or empty set; same instances
-- source:
--   Horodecki, Horodecki, Horodecki, Oppenheim, Secure key from bound entanglement, arXiv:quant-ph/0309110v2, Main result, eqs. (11)–(13), p.3 (with (9), p.2, (10), p.3, and the abstract, p.1)

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P24
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P42
import Definitions.Def_HorodeckiBoundKey_finCut
import Definitions.Def_HorodeckiBoundKey_IsSeparable

open QAlgorithms QAlgorithms.Papers.Independent
open QAlgorithms.Papers.Independent.Information100.P21 (Op)
open scoped Matrix ComplexOrder ENNReal
open QAlgorithms.Papers.Independent.Dependency50.P24 (hidingFamily transposeBob)
open QAlgorithms.Papers.Independent.Gap48.P42 (distillableKey bipartiteDistillable)

namespace HorodeckiBoundKey

/-- Horodecki, Horodecki, Horodecki, Oppenheim, *Secure key from bound entanglement*,
arXiv:quant-ph/0309110v2, Main result, eqs. (11)–(13), p.3: "We now introduce a bound entangled
state which can be shown to have K_D > 0." Abstract (p.1): "It is shown that one can distill an
arbitrarily secure key from bound entangled states."

For every real `p` with `1/4 < p ≤ 1/3` there are integers `l ≥ 1` and `d ≥ 2` such that the
state `ρ = ρ(p, d, l)` of (11) on `A B A′ B′`, built from the hiding states (10)
`τ₀ = ϱ_s^{⊗l}`, `τ₁ = [(ϱ_a + ϱ_s)/2]^{⊗l}` of `d ⊗ d` Werner states (9), is
1. a state (positive semidefinite, trace one);
2. PPT across `AA′ : BB′`;
3. not separable across `AA′ : BB′`;
4. of zero distillable entanglement, `E_D(ρ) = 0`;
5. of strictly positive distillable key, `K_D(ρ) > 0`.

Clauses 1–4 are "bound entangled" (p.1: "states which require entanglement to create, but from
which no pure entanglement can be distilled").

**Formalization Note.** `ρ` is the published `Dependency50.P24.hidingFamily p d l`, with
`hidingTwo = τ₀`, `hidingOne = τ₁`, registers `Key 2 × (A′ × B′)` (`A′` = Alice's `l` qudits,
`B′` = Bob's). PPT is `transposeBob` (transpose of `B` and `B′` together). The Alice:Bob cut
is `finCut`. `K_D` is read as `K_γ` (p.2: "We thus have equality of the two rates"; "Clearly
K_γ ≤ K_D"), the operational private-dit rate `Gap48.P42.distillableKey` under deterministic
finite adaptive LOCC; `E_D` is the Bell-pair rate `Gap48.P42.bipartiteDistillable`. Both rates
are `ℝ≥0∞` suprema. -/
theorem main_result :
    ∀ p : ℝ, 1 / 4 < p → p ≤ 1 / 3 →
      ∃ l d : ℕ, 1 ≤ l ∧ 2 ≤ d ∧
        IsDensityMatrix (hidingFamily p d l) ∧
        (transposeBob (hidingFamily p d l)).PosSemidef ∧
        ¬ IsSeparable (finCut (hidingFamily p d l)) ∧
        bipartiteDistillable (finCut (hidingFamily p d l)) = 0 ∧
        0 < distillableKey (finCut (hidingFamily p d l)) := by sorry

end HorodeckiBoundKey
