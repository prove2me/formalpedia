-- Prove2me | Theorems.Thm_ModularCurve_natCard_heckeTorsion_span_sup_eq_sq_natCard_heckeLatticeAlgebra_quotient
-- name    : ModularCurve.natCard_heckeTorsion_span_sup_eq_sq_natCard_heckeLatticeAlgebra_quotient
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.624895+00:00
-- url     : https://prove2.me/theorems/ecccf7d0-a52c-5402-b5af-677f0d563a7b
-- title:
--   Eisenstein torsion of J₀(p) counted as a square
-- statement:
--   Let $p$ and $q$ be primes with $q \neq p$. Write $\mathbb{T} =$ `HeckeAlg` $= \mathrm{MvPolynomial}\ \mathrm{Nat.Primes}\ \mathbb{Z}$, the polynomial ring over $\mathbb{Z}$ on one variable per prime, and let $\mathfrak{P} =$ `eisensteinMaximalIdeal p q` be the preimage under the $\mathbb{Z}$-algebra map `eisensteinEval p` $: \mathbb{T} \to \mathbb{Z}$ of the ideal $(q) \subseteq \mathbb{Z}$. The group `JZero p` is the degree-zero divisor class group $\mathrm{Pic}^0$ of the base-changed modular function field at level $p$ over $\overline{\mathbb{Q}}$, regarded as a $\mathbb{T}$-module via `heckeModuleBar p`. On the other side, `heckeLatticeAlgebra p ∅` is the $\mathbb{Z}$-subalgebra of $\mathrm{End}_{\mathbb{Z}}(\mathrm{intLattice}\ p\ 2)$ given by the image of the weight-two Hecke algebra of $\Gamma_0(p)$ (with empty excluded set) acting on the lattice spanned by cusp forms with integral $q$-expansion coefficients, and $\varphi$ denotes the composite of `heckeEvalForms p 2` $: \mathbb{T} \to$ `heckeAlgebra p 2 ∅` (sending the variable at $\ell$ to $U_\ell$ if $\ell \mid p$ and to $T_\ell$ otherwise) with the range restriction `latticeRestrictHom p ∅`. The assertion is: for all natural numbers $k$ and $M$, if the submodule of `JZero p` annihilated by $(q^k) + \mathfrak{P}^{M+1}$ equals that annihilated by $(q^k) + \mathfrak{P}^{M}$, and if $(q^k) + (\varphi_*\mathfrak{P})^{M+1} = (q^k) + (\varphi_*\mathfrak{P})^{M}$ as ideals of `heckeLatticeAlgebra p ∅`, then the cardinality of the submodule of `JZero p` annihilated by $(q^k) + \mathfrak{P}^{M}$ equals the square of the cardinality of `heckeLatticeAlgebra p ∅` modulo $(q^k) + (\varphi_*\mathfrak{P})^{M}$.
--
--   This is the total-count statement in Mazur's study of the Eisenstein ideal: at a stable exponent $M$, the Eisenstein-component $q^k$-torsion of $J_0(p)$ has order the square of the order of the corresponding quotient of the integral weight-two Hecke lattice algebra, the exponent $2$ reflecting the rank-two Eichler–Shimura comparison. It feeds the inequality [`ModularCurve.natCard_heckeLatticeAlgebra_quotient_le_natCard_image_reductionModL_heckeTorsion_span_sup`](thm.html#ModularCurve.natCard_heckeLatticeAlgebra_quotient_le_natCard_image_reductionModL_heckeTorsion_span_sup).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_natCard_heckeTorsion_span_sup_eq_sq_natCard_heckeLatticeAlgebra_quotient.lean

import Definitions.Def_ModularCurve_JZeroNeronTorsionSheafV4
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_CuspForm_HeckeLocal
import Definitions.Def_CuspForm_HeckeEvalForms

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open ModularCurve CuspForm

theorem ModularCurve.natCard_heckeTorsion_span_sup_eq_sq_natCard_heckeLatticeAlgebra_quotient
    (p : ℕ) [Fact p.Prime] (q : ℕ) [Fact q.Prime] (hqp : q ≠ p) :
    letI := heckeModuleBar p
    ∀ k M : ℕ,
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
      Nat.card ↥(heckeTorsion (JZero p)
          (Ideal.span {((q : ℕ) ^ k : HeckeAlg)} ⊔ (eisensteinMaximalIdeal p q) ^ M)) =
        Nat.card (↥(heckeLatticeAlgebra p ∅) ⧸
          (Ideal.span {((q : ℕ) ^ k : ↥(heckeLatticeAlgebra p ∅))} ⊔
            (Ideal.map ((latticeRestrictHom p ∅).toRingHom.comp (heckeEvalForms p 2))
              (eisensteinMaximalIdeal p q)) ^ M)) ^ 2 := by sorry
