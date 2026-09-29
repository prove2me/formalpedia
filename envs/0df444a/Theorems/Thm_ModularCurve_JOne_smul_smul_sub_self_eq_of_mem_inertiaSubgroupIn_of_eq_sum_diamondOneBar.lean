-- Prove2me | Theorems.Thm_ModularCurve_JOne_smul_smul_sub_self_eq_of_mem_inertiaSubgroupIn_of_eq_sum_diamondOneBar
-- name    : ModularCurve.JOne.smul_smul_sub_self_eq_of_mem_inertiaSubgroupIn_of_eq_sum_diamondOneBar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.860483+00:00
-- url     : https://prove2.me/theorems/9e27dc6c-2edd-50ed-b18b-e514f8ee033a
-- title:
--   Inertia at q acts unipotently on diamond-norms of prime-to-q torsion
-- statement:
--   Let $M_0 \ge 1$ and let $q$ be a prime with $q \nmid M_0$; put $M = M_0 q$. Assume `hdia`: for every $d$ coprime to $M$ there is a $\mathbb{Q}$-algebra automorphism of [`ModularCurve.x1FunctionField M`](def/ModularCurve_X1.html#L137) — the $q$-expansion function field of $X_1(M)$ inside $\mathbb{Q}((q))$ — satisfying [`ModularCurve.IsDiamondAut M d`](def/ModularCurve_X1Diamond.html#L53), i.e. $d$ is coprime to $M$ and, for all weights $k$, all weight-$k$ forms $f,g$ on $\Gamma_1(M)$ with integral $q$-expansions $p_f,p_g$ and $p_g$ giving a nonzero series, and all $\gamma \in \Gamma_0(M)$ with upper-left entry $\equiv d \bmod M$, the image of $p_f/p_g$ under the automorphism times the $q$-expansion of $g|_k\gamma$ equals that of $f|_k\gamma$; and there is an automorphism of the base-changed field [`ModularCurve.x1FunctionFieldBar M`](def/ModularCurve_X1.html#L182) over $\overline{\mathbb{Q}}$ which is a base change of [`ModularCurve.diamondAut M d`](def/ModularCurve_X1Diamond.html#L66), i.e. agrees with it coefficientwise on the image of $\mathbb{Q}((q))$-coefficient embedding. Let $P$ be a valuation subring of $\overline{\mathbb{Q}}$ with $q$ a nonunit of $P$, and let $\sigma,\tau$ lie in the image in $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ of the inertia subgroup of $P$. Let $x$ be an element of [`ModularCurve.JOne M`](def/ModularCurve_X1.html#L186), the group of degree-zero divisor classes of [`ModularCurve.x1FunctionFieldBar M`](def/ModularCurve_X1.html#L182) over $\overline{\mathbb{Q}}$, killed by an integer $n$ with $q \nmid n$, and set $y = \sum_d \langle d\rangle_* x$, the sum over $0 \le d < M$ coprime to $M$ with $d \equiv 1 \bmod M_0$ of the $\mathbb{Z}$-linear diamond endomorphisms [`ModularCurve.diamondOneBar M d`](def/ModularCurve_X1Diamond.html#L98). Then $\tau \cdot (\sigma \cdot y - y) = \sigma \cdot y - y$.
--
--   This is the Deligne–Rapoport semistable reduction theorem for $X(\Gamma_1(M_0) \cap \Gamma_0(q))$ at $q$, combined with Grothendieck's description of the inertia action on prime-to-$q$ torsion of a semistably reducing abelian variety ($\sigma \mapsto 1 + N_\sigma$ with $N_\tau N_\sigma = 0$), transported to $J_1(M_0 q)$ along the diamond-norm map onto the part coming from the intermediate curve. It is used in the proof that the $\ell$-adic representation attached to a primitive form is unipotent on inertia at primes dividing the level exactly once.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JOne_smul_smul_sub_self_eq_of_mem_inertiaSubgroupIn_of_eq_sum_diamondOneBar.lean

import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_ModularCurve_X1Diamond

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.JOne.smul_smul_sub_self_eq_of_mem_inertiaSubgroupIn_of_eq_sum_diamondOneBar
    (M₀ q : ℕ) [NeZero M₀] (hq : q.Prime) (hqM₀ : ¬ q ∣ M₀)
    (hdia : ∀ d : ℕ, Nat.Coprime d (M₀ * q) →
      (∃ σ₀ : ModularCurve.x1FunctionField (M₀ * q) ≃ₐ[ℚ] ModularCurve.x1FunctionField (M₀ * q),
          ModularCurve.IsDiamondAut (M₀ * q) d σ₀) ∧
        ∃ σ' : ModularCurve.x1FunctionFieldBar (M₀ * q) ≃ₐ[AlgebraicClosure ℚ]
            ModularCurve.x1FunctionFieldBar (M₀ * q),
          ModularCurve.IsBaseChangeAutOf (AlgebraicClosure ℚ)
            (ModularCurve.diamondAut (M₀ * q) d) σ')
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime q)
    (σ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (hσ : σ ∈ P.inertiaSubgroupIn ℚ) (hτ : τ ∈ P.inertiaSubgroupIn ℚ)
    (x : ModularCurve.JOne (M₀ * q)) (n : ℕ) (hn : ¬ q ∣ n) (hx : (n : ℤ) • x = 0)
    (y : ModularCurve.JOne (M₀ * q))
    (hy : y = ∑ d ∈ (Finset.range (M₀ * q)).filter (fun d => Nat.Coprime d (M₀ * q) ∧ d ≡ 1 [MOD M₀]),
            ModularCurve.diamondOneBar (M₀ * q) d x) :
    τ • (σ • y - y) = σ • y - y := by sorry
