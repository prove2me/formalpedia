-- Prove2me | Theorems.Thm_ModularCurve_exists_character_generator_heckeTorsion_span_sup_inertiaSubgroupIn_of_ne_two
-- name    : ModularCurve.exists_character_generator_heckeTorsion_span_sup_inertiaSubgroupIn_of_ne_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.209688+00:00
-- url     : https://prove2.me/theorems/58b58b4a-b511-59e9-aaf0-e67ac78de8ff
-- title:
--   Character detecting inertia eigenvectors in Eisenstein torsion, q odd
-- statement:
--   Fix primes $p$ and $q$ with $q \neq 2$ and $q \neq p$, and a valuation subring $A_q$ of $\overline{\mathbf{Q}} =$ `AlgebraicClosure ℚ` with $q$ in its nonunits. Write $J =$ `JZero p`, the degree-zero divisor class group of the level-$p$ modular function field over $\overline{\mathbf{Q}}$, a module over `HeckeAlg` $= \mathbf{Z}[X_\ell : \ell \text{ prime}]$ via `heckeModuleBar p`, and $\mathfrak{P} =$ `eisensteinMaximalIdeal p q`, the preimage under `eisensteinEval p` of $(q) \subseteq \mathbf{Z}$. Let $k, M \in \mathbf{N}$ and let $n \colon \mathrm{Gal}(\overline{\mathbf{Q}}/\mathbf{Q}) \to \mathbf{N}$ satisfy $\sigma\zeta = \zeta^{n\sigma}$ for every $\sigma$ and every $\zeta$ with $\zeta^{q^k} = 1$. Assume the tower is stable at $M$ in two senses: the submodule of $J$ annihilated by $(q^k) + \mathfrak{P}^{M+1}$ equals that annihilated by $(q^k) + \mathfrak{P}^{M}$, and in `heckeLatticeAlgebra p ∅` — the image of the weight-two level-$p$ Hecke algebra acting on the integral cusp-form lattice — the ideals $(q^k) + \mathfrak{P}_0^{M+1}$ and $(q^k) + \mathfrak{P}_0^{M}$ agree, $\mathfrak{P}_0$ being the image of $\mathfrak{P}$ under `heckeEvalForms p 2` followed by `latticeRestrictHom p ∅`. Then, writing $T$ for the $((q^k) + \mathfrak{P}^M)$-torsion of $J$, there is a map $e_0 \colon T \to \overline{\mathbf{Q}}^\times$ with $e_0(v_1 + v_2) = e_0(v_1)e_0(v_2)$, such that $e_0(v) = 1$ whenever $\sigma \cdot v = (n\sigma) \cdot v$ for all $\sigma$ in `Aq.inertiaSubgroupIn ℚ`, and conversely such that if $e_0(t \cdot v) = 1$ for every $t \in$ `HeckeAlg` then $\sigma \cdot v = (n\sigma) \cdot v$ for all such $\sigma$.
--
--   This is the multiplicity-one input of Mazur's study of the Eisenstein ideal, in the form that the character group dual to the inertia-fixed part of the Eisenstein torsion tower is cyclic over the Hecke algebra, equivalently that the étale quotient at an odd prime $q \neq p$ has simple socle. It is used in the construction of a free character and of the pairing on the Eisenstein torsion modulo the lattice Hecke algebra.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_character_generator_heckeTorsion_span_sup_inertiaSubgroupIn_of_ne_two.lean

import Definitions.Def_ModularCurve_JZeroNeronTorsionSheafV4
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_CuspForm_HeckeLocal
import Definitions.Def_CuspForm_HeckeEvalForms

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve CuspForm

theorem ModularCurve.exists_character_generator_heckeTorsion_span_sup_inertiaSubgroupIn_of_ne_two
    (p : ℕ) [Fact p.Prime] (q : ℕ) [Fact q.Prime] (hq2 : q ≠ 2) (hqp : q ≠ p)
    (Aq : ValuationSubring (AlgebraicClosure ℚ)) (_hAq : Aq.LiesOverPrime q) :
    letI := heckeModuleBar p
    ∀ k M : ℕ, ∀ n : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → ℕ,
      (∀ σ, ∀ ζ : AlgebraicClosure ℚ, ζ ^ (q ^ k) = 1 → σ ζ = ζ ^ n σ) →
      heckeTorsion (JZero p)
          (Ideal.span {((q : ℕ) ^ k : HeckeAlg)} ⊔ (eisensteinMaximalIdeal p q) ^ (M + 1)) =
        heckeTorsion (JZero p)
          (Ideal.span {((q : ℕ) ^ k : HeckeAlg)} ⊔ (eisensteinMaximalIdeal p q) ^ M) →
      (Ideal.span {((q : ℕ) ^ k : ↥(heckeLatticeAlgebra p ∅))} ⊔
          (Ideal.map ((latticeRestrictHom p ∅).toRingHom.comp (heckeEvalForms p 2))
            (eisensteinMaximalIdeal p q)) ^ (M + 1)) =
        (Ideal.span {((q : ℕ) ^ k : ↥(heckeLatticeAlgebra p ∅))} ⊔
          (Ideal.map ((latticeRestrictHom p ∅).toRingHom.comp (heckeEvalForms p 2))
            (eisensteinMaximalIdeal p q)) ^ M) →
      ∃ e₀ : ↥(heckeTorsion (JZero p)
              (Ideal.span {((q : ℕ) ^ k : HeckeAlg)} ⊔ (eisensteinMaximalIdeal p q) ^ M)) →
            (AlgebraicClosure ℚ)ˣ,
        (∀ v₁ v₂, e₀ (v₁ + v₂) = e₀ v₁ * e₀ v₂) ∧
        (∀ v : ↥(heckeTorsion (JZero p)
              (Ideal.span {((q : ℕ) ^ k : HeckeAlg)} ⊔ (eisensteinMaximalIdeal p q) ^ M)),
          (∀ σ ∈ Aq.inertiaSubgroupIn ℚ,
            σ • (v : JZero p) = n σ • (v : JZero p)) → e₀ v = 1) ∧
        (∀ v, (∀ t : HeckeAlg, e₀ (t • v) = 1) →
          ∀ σ ∈ Aq.inertiaSubgroupIn ℚ, σ • (v : JZero p) = n σ • (v : JZero p)) := by sorry
