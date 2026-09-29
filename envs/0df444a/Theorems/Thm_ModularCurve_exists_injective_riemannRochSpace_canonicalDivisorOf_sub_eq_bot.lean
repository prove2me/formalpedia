-- Prove2me | Theorems.Thm_ModularCurve_exists_injective_riemannRochSpace_canonicalDivisorOf_sub_eq_bot
-- name    : ModularCurve.exists_injective_riemannRochSpace_canonicalDivisorOf_sub_eq_bot
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.587938+00:00
-- url     : https://prove2.me/theorems/9abd208a-cc27-5d12-95af-d1d12d82bbf2
-- title:
--   Auxiliary places making K-E non-special on X₀(N)
-- statement:
--   Let $N \ge 1$ and let $\bar F_N$ denote `modularFunctionFieldBar N`, the subfield of the Laurent series field over $\overline{\mathbb{Q}}$ generated over $\overline{\mathbb{Q}}$ by the coefficientwise image of the full modular function field of level $N$; assume the class `HasCanonicalDivisor` for $\bar F_N/\overline{\mathbb{Q}}$, i.e. that for every nonzero Kähler differential there is a divisor whose value at each place $v$ is $v.\mathrm{ordDifferential}$ of that differential. Let $\omega \neq 0$ be a differential of $\bar F_N$ over $\overline{\mathbb{Q}}$, with associated divisor $K_0 =$ `canonicalDivisorOf hω`; let $n$ be a natural number and $E$ a divisor, that is a finitely supported integer-valued function on the places of $\bar F_N/\overline{\mathbb{Q}}$ (places being proper valuation subrings containing $\overline{\mathbb{Q}}$ and principal ideal rings), which is effective, $0 \le E$ pointwise, and such that the Riemann–Roch space of $K_0 - E$ — the $\overline{\mathbb{Q}}$-subspace of $f$ with $v(f) \le \exp((K_0-E)(v))$ at every place $v$ — has $\overline{\mathbb{Q}}$-dimension $n$. Let $\mathcal{Q}$ be a finite set of places with $2g \le \#\mathcal{Q} + 1$, where $g$ is `genusFF`, the $\overline{\mathbb{Q}}$-dimension of $H^1$ of the zero divisor. Then there is an injective family $Q : \mathrm{Fin}\, n \to \mathrm{Place}$ with every $Q_l \in \mathcal{Q}$ and $Q_l \notin \operatorname{supp} E$, such that the Riemann–Roch space of $K_0 - E - \sum_l Q_l$ is the zero submodule.
--
--   This is the standard device of cutting down a special divisor by imposing extra degree-one conditions: starting from $K_0-E$ on the curve $X_0(N)$ over $\overline{\mathbb{Q}}$, one finds $n$ distinct auxiliary places inside a prescribed finite pool $\mathcal{Q}$, avoiding the support of $E$, which kill the whole Riemann–Roch space. It is used in the height-form estimates for points of $X_0(N)$, in [`ModularCurve.JZero.exists_baseMass_le_heightForm_of_exists_two_le`](thm.html#ModularCurve.JZero.exists_baseMass_le_heightForm_of_exists_two_le) and [`ModularCurve.JZero.exists_sum_pairHt_le_of_forall_le_one`](thm.html#ModularCurve.JZero.exists_sum_pairHt_le_of_forall_le_one).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_injective_riemannRochSpace_canonicalDivisorOf_sub_eq_bot.lean

import Definitions.Def_ModularCurve_JZeroHeightForm
import Definitions.Def_AlgebraicCurve_CanonicalDivisor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem ModularCurve.exists_injective_riemannRochSpace_canonicalDivisorOf_sub_eq_bot (N : ℕ) [NeZero N]
    [HasCanonicalDivisor (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar N))]
    {ω : Ω[↥(modularFunctionFieldBar N)⁄(AlgebraicClosure ℚ)]} (hω : ω ≠ 0) {n : ℕ}
    {E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)} (hE : 0 ≤ E)
    (hn : Module.finrank (AlgebraicClosure ℚ)
        ↥(riemannRochSpace (canonicalDivisorOf hω - E)) = n)
    (𝒬 : Finset (Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)))
    (h𝒬 : 2 * genusFF (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) ≤ 𝒬.card + 1) :
    ∃ Q : Fin n → Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      Function.Injective Q ∧ (∀ l, Q l ∈ 𝒬 ∧ Q l ∉ E.support) ∧
      riemannRochSpace (canonicalDivisorOf hω - E - ∑ l, Finsupp.single (Q l) (1 : ℤ)) = ⊥ := by sorry
