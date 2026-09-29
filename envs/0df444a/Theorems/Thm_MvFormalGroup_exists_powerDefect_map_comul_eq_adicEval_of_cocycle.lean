-- Prove2me | Theorems.Thm_MvFormalGroup_exists_powerDefect_map_comul_eq_adicEval_of_cocycle
-- name    : MvFormalGroup.exists_powerDefect_map_comul_eq_adicEval_of_cocycle
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.856965+00:00
-- url     : https://prove2.me/theorems/b9e431e1-d70c-5449-ab6e-4ff584063f29
-- title:
--   Power defects of a symmetric 2-cocycle over a p-divisible tower
-- statement:
--   Let $\mathcal O$ be a commutative ring and $p$ a prime such that $p$ is a non-zero-divisor in $\mathcal O$, the ideal $(p)$ is maximal, and $\mathcal O$ is $(p)$-adically complete; let $\Phi$ be a commutative $d$-dimensional formal group law over $\mathcal O$, i.e. a $d$-tuple of power series in $2d$ variables with zero constant term, identity linear part in each block of variables, satisfying associativity and the symmetry $\Phi(Y,X)=\Phi(X,Y)$. Let $E_v$ ($v\in\mathbb N$) be commutative cocommutative Hopf $\mathcal O$-algebras, finite and free as $\mathcal O$-modules, with surjective bialgebra maps $st_v : E_{v+1}\to E_v$ whose kernels are the images of the augmentation ideal $\ker\varepsilon$ under the $p^v$-th convolution power of the identity. Let $c_2^{(v)}\in (E_v\otimes_{\mathcal O}E_v)^d$ be tuples satisfying: compatibility $(st_v\otimes st_v)(c_2^{(v+1)})=c_2^{(v)}$; divisibility $c_2^{(v)}\in(p)$; normalisation, symmetry and the $2$-cocycle identity $c_2(f,f')+_\Phi c_2(ff',f'')=c_2(f',f'')+_\Phi c_2(f,f'f'')$, all three read on $\mathcal O$-algebra points $f,f',f''\colon E_v\to g$ valued in commutative $\mathcal O$-algebras $g$ in which $p$ is a non-zero-divisor and which are $(p)$-adically complete, with $+_\Phi$ meaning $(p)$-adic evaluation of $\Phi$. Then there exist tuples $C_{v,n}\in E_v^d$ with $C_{v,0}=0$ and $C_{v,n+1}=C_{v,n}+_\Phi m\bigl(([n]^{*}\otimes\mathrm{id})c_2^{(v)}\bigr)$, where $[n]^{*}$ is the $n$-th convolution power of $\mathrm{id}_{E_v}$ and $m$ the multiplication of $E_v$, such that $C_{v,n}\in(p)$, $\varepsilon(C_{v,n})=0$, $st_v(C_{v+1,n})=C_{v,n}$, $C_{v,p^vm}=[m]_\Phi(C_{v,p^v})$ (iterated group law), and, in $E_v\otimes_{\mathcal O}E_v$, $\Delta(C_{v,n})+_\Phi[n]_\Phi c_2^{(v)}=(C_{v,n}\otimes 1)+_\Phi\bigl((1\otimes C_{v,n})+_\Phi([n]^{*}\otimes[n]^{*})c_2^{(v)}\bigr)$.
--
--   The tuples $C_{v,n}$ are the power defects (carries) of the twisted group law $(f,x)(f',x')=(ff',x+_\Phi x'+_\Phi c_2(f,f'))$, for which $(f,x)^n=(f^n,[n]_\Phi x+_\Phi C_n(f))$; the listed clauses record the group axioms at universal points together with compatibility along the tower and divisibility by $p$. The result is used by [`MvFormalGroup.exists_pDivisibleTower_of_cocycle`](thm.html#MvFormalGroup.exists_pDivisibleTower_of_cocycle) to build the twisted tower of Hopf algebras attached to a $2$-cocycle.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MvFormalGroup_exists_powerDefect_map_comul_eq_adicEval_of_cocycle.lean

import Mathlib
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_MvFormalGroup_BasicV2
import Definitions.Def_MvFormalGroup_EndRingV2
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_PointsV2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct
open MvPowerSeries

universe u

theorem MvFormalGroup.exists_powerDefect_map_comul_eq_adicEval_of_cocycle
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    [(Ideal.span {(p : 𝓞)}).IsMaximal] [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
    {d : ℕ} (Φ : MvFormalGroup d 𝓞) [Φ.IsComm]

    (E : ℕ → Type u) [∀ v, CommRing (E v)] [∀ v, HopfAlgebra 𝓞 (E v)]
    [∀ v, Coalgebra.IsCocomm 𝓞 (E v)] [∀ v, Module.Free 𝓞 (E v)] [∀ v, Module.Finite 𝓞 (E v)]
    (st : ∀ v, E (v + 1) →ₐc[𝓞] E v) (hst : ∀ v, Function.Surjective (st v))
    (hkerE : ∀ v, RingHom.ker (st v) = PDivisibleGroup.Hopf.torsionIdeal 𝓞 (E (v + 1)) (p ^ v))

    (c₂ : ∀ v, Fin d → E v ⊗[𝓞] E v)
    (hCOC :
      (∀ v i, Algebra.TensorProduct.map (st v : E (v + 1) →ₐ[𝓞] E v)
          (st v : E (v + 1) →ₐ[𝓞] E v) (c₂ (v + 1) i) = c₂ v i) ∧
      (∀ v i, c₂ v i ∈ Ideal.span {(p : E v ⊗[𝓞] E v)}) ∧
      (∀ (g : Type u) [CommRing g] [Algebra 𝓞 g], (p : g) ∈ nonZeroDivisors g →
        IsAdicComplete (Ideal.span {(p : g)}) g → ∀ (v : ℕ) (f : E v →ₐ[𝓞] g) (j : Fin d),
          Algebra.TensorProduct.lift f ((Algebra.ofId 𝓞 g).comp (Bialgebra.counitAlgHom 𝓞 (E v))) (fun _ _ => Commute.all _ _) (c₂ v j) = 0 ∧
          Algebra.TensorProduct.lift ((Algebra.ofId 𝓞 g).comp (Bialgebra.counitAlgHom 𝓞 (E v))) f (fun _ _ => Commute.all _ _) (c₂ v j) = 0) ∧
      (∀ (g : Type u) [CommRing g] [Algebra 𝓞 g], (p : g) ∈ nonZeroDivisors g →
        IsAdicComplete (Ideal.span {(p : g)}) g → ∀ (v : ℕ) (f f' : E v →ₐ[𝓞] g) (j : Fin d),
          Algebra.TensorProduct.lift f f' (fun _ _ => Commute.all _ _) (c₂ v j) = Algebra.TensorProduct.lift f' f (fun _ _ => Commute.all _ _) (c₂ v j)) ∧
      (∀ (g : Type u) [CommRing g] [Algebra 𝓞 g], (p : g) ∈ nonZeroDivisors g →
        IsAdicComplete (Ideal.span {(p : g)}) g → ∀ (v : ℕ) (f f' f'' : E v →ₐ[𝓞] g),
          (fun i => MvFormalGroup.adicEval (Ideal.span {(p : g)}) (Sum.elim ((fun j => Algebra.TensorProduct.lift f f' (fun _ _ => Commute.all _ _) (c₂ v j))) ((fun j => Algebra.TensorProduct.lift ((Algebra.TensorProduct.lift f f' (fun _ _ => Commute.all _ _)).comp (Bialgebra.comulAlgHom 𝓞 (E v))) f'' (fun _ _ => Commute.all _ _) (c₂ v j)))) (Φ.toPowerSeries i)) =
          (fun i => MvFormalGroup.adicEval (Ideal.span {(p : g)}) (Sum.elim ((fun j => Algebra.TensorProduct.lift f' f'' (fun _ _ => Commute.all _ _) (c₂ v j))) ((fun j => Algebra.TensorProduct.lift f ((Algebra.TensorProduct.lift f' f'' (fun _ _ => Commute.all _ _)).comp (Bialgebra.comulAlgHom 𝓞 (E v))) (fun _ _ => Commute.all _ _) (c₂ v j)))) (Φ.toPowerSeries i)))) :
    ∃ C : ∀ v, ℕ → Fin d → E v,

      (∀ v i, C v 0 i = 0) ∧
      (∀ v n i, C v (n + 1) i =
        MvFormalGroup.adicEval (Ideal.span {(p : E v)})
          (Sum.elim (C v n) (fun j => Algebra.TensorProduct.lmul' 𝓞 (S := E v)
            (Algebra.TensorProduct.map (PDivisibleGroup.Hopf.nsmulAlgHom 𝓞 (E v) n) (AlgHom.id 𝓞 (E v))
              (c₂ v j))))
          (Φ.toPowerSeries i)) ∧

      (∀ v n i, C v n i ∈ Ideal.span {(p : E v)}) ∧
      (∀ v n i, Coalgebra.counit (R := 𝓞) (C v n i) = 0) ∧

      (∀ v n i, st v (C (v + 1) n i) = C v n i) ∧
      (∀ v m i, C v (p ^ v * m) i =
        MvFormalGroup.adicEval (Ideal.span {(p : E v)}) (C v (p ^ v)) (Φ.nthSeries m i)) ∧

      (∀ v n i,
        MvFormalGroup.adicEval (Ideal.span {(p : E v ⊗[𝓞] E v)})
          (Sum.elim (fun j => Coalgebra.comul (R := 𝓞) (C v n j))
            (fun j => MvFormalGroup.adicEval (Ideal.span {(p : E v ⊗[𝓞] E v)}) (c₂ v) (Φ.nthSeries n j)))
          (Φ.toPowerSeries i) =
        MvFormalGroup.adicEval (Ideal.span {(p : E v ⊗[𝓞] E v)})
          (Sum.elim (fun j => C v n j ⊗ₜ[𝓞] (1 : E v))
            (fun j => MvFormalGroup.adicEval (Ideal.span {(p : E v ⊗[𝓞] E v)})
              (Sum.elim (fun j => (1 : E v) ⊗ₜ[𝓞] C v n j)
                (fun j => Algebra.TensorProduct.map (PDivisibleGroup.Hopf.nsmulAlgHom 𝓞 (E v) n)
                  (PDivisibleGroup.Hopf.nsmulAlgHom 𝓞 (E v) n) (c₂ v j)))
              (Φ.toPowerSeries j)))
          (Φ.toPowerSeries i)) := by sorry
