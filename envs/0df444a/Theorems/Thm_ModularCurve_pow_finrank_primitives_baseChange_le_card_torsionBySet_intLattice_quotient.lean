-- Prove2me | Theorems.Thm_ModularCurve_pow_finrank_primitives_baseChange_le_card_torsionBySet_intLattice_quotient
-- name    : ModularCurve.pow_finrank_primitives_baseChange_le_card_torsionBySet_intLattice_quotient
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.985053+00:00
-- url     : https://prove2.me/theorems/4fd72c7a-0d8c-5a86-87e3-19155c3cbd31
-- title:
--   Primitives of a finite flat model bounded by (S/pS)[𝔪]
-- statement:
--   Fix $N\ge 1$ and a prime $p$ with $p\neq 2$ and $p\nmid N$, and let $\mathfrak m$ be an ideal of the Hecke algebra `HeckeAlg`, the polynomial ring $\mathbf Z[X_\ell:\ell\text{ prime}]$, containing the constant $p$. Write $\mathbf Z_{(p)}$ for [`GaloisRep.ratLocalizedAt p`](def/GaloisRep_Flat.html#L8), the subring of rationals whose denominator is coprime to $p$. Let $H$ be a commutative ring carrying a Hopf algebra structure over $\mathbf Z_{(p)}$ that is finite and flat as a $\mathbf Z_{(p)}$-module and whose comultiplication is cocommutative, and let $k_0$ be a field of characteristic $p$ with a $\mathbf Z_{(p)}$-algebra structure. Here `JZero N` is the degree-zero divisor class group $\mathrm{Pic}^0$ of the base change to $\overline{\mathbf Q}$ of the modular function field of level $N$, a `HeckeAlg`-module through `heckeModuleBar N` (evaluation of the variables at the Hecke operators when these commute, and the trivial action otherwise), and [`CuspForm.intLattice N 2`](def/CuspForm_IntegralStructure.html#L3) is the $\mathbf Z$-span of those weight-two cusp forms on $\Gamma_0(N)$ all of whose $q$-expansion coefficients are integers, a `HeckeAlg`-module through `(CuspForm.latticeHeckeFamily N).module`, in which the variable indexed by $\ell$ acts by $U_\ell$ if $\ell\mid N$ and by $T_\ell$ otherwise. The assertion is: for every bijection $e$ from `WithConv` of the set of $\mathbf Z_{(p)}$-algebra maps $H\to\overline{\mathbf Q}$ (that set with its convolution multiplication) onto the $\mathfrak m$-torsion $\{x : t\cdot x=0\ \forall t\in\mathfrak m\}$ of `JZero N`, such that $e(fg)=e(f)+e(g)$ for all $f,g$, and such that for every $\sigma\in\mathrm{Gal}(\overline{\mathbf Q}/\mathbf Q)$ and all $f,g$ with $g(h)=\sigma(f(h))$ for all $h\in H$ one has $e(g)=\sigma\cdot e(f)$ in `JZero N`, the inequality $$p^{\dim_{k_0} P(k_0\otimes_{\mathbf Z_{(p)}}H)}\ \le\ \#\bigl(S/pS\bigr)[\mathfrak m]$$ holds, where $P(-)$ denotes the primitive elements, i.e. the kernel of $a\mapsto \Delta(a)-a\otimes 1-1\otimes a$, $S=$ [`CuspForm.intLattice N 2`](def/CuspForm_IntegralStructure.html#L3), $pS$ is the submodule `Ideal.span {p} • ⊤`, and $[\mathfrak m]$ denotes $\mathfrak m$-torsion.
--
--   This is the inequality half of Mazur's comparison (14.3) in Chapter II, §14 of *Modular curves and the Eisenstein ideal*: the primitives of the special fibre of a finite flat $\mathbf Z_{(p)}$-model of $J_0(N)[\mathfrak m]$ are bounded by the $\mathfrak m$-torsion of weight-two cusp forms with integral $q$-expansion modulo $p$. It feeds the estimate on the Dieudonné module modulo the image of Verschiebung used in the local–local analysis of such models.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_pow_finrank_primitives_baseChange_le_card_torsionBySet_intLattice_quotient.lean

import Definitions.Def_Dieudonne_ModpRealization
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_CuspForm_LatticeHeckeFamily

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve
open scoped TensorProduct

theorem ModularCurve.pow_finrank_primitives_baseChange_le_card_torsionBySet_intLattice_quotient
    (N : ℕ) [NeZero N] (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hpN : ¬ p ∣ N)
    (𝔪 : Ideal HeckeAlg) (hpm : (p : HeckeAlg) ∈ 𝔪)
    (H : Type) [CommRing H] [HopfAlgebra (GaloisRep.ratLocalizedAt p) H]
    [Module.Finite (GaloisRep.ratLocalizedAt p) H] [Module.Flat (GaloisRep.ratLocalizedAt p) H]
    [Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt p) H]
    (k₀ : Type) [Field k₀] [CharP k₀ p] [Algebra (GaloisRep.ratLocalizedAt p) k₀] :
    letI := heckeModuleBar N
    letI := (CuspForm.latticeHeckeFamily N).module
    ∀ e : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) ≃
        ↥(heckeTorsion (JZero N) 𝔪),
      (∀ f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ),
          e (f * g) = e f + e g) →
      (∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
          (f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)),
          (∀ h : H, g h = σ (f h)) → ((e g : JZero N)) = σ • (e f : JZero N)) →
      p ^ Module.finrank k₀ ↥(primitives k₀ (k₀ ⊗[GaloisRep.ratLocalizedAt p] H))
        ≤ Nat.card ↥(Submodule.torsionBySet HeckeAlg
            (↥(CuspForm.intLattice N 2) ⧸ (Ideal.span {((p : ℕ) : HeckeAlg)} •
              (⊤ : Submodule HeckeAlg ↥(CuspForm.intLattice N 2)))) 𝔪) := by sorry
