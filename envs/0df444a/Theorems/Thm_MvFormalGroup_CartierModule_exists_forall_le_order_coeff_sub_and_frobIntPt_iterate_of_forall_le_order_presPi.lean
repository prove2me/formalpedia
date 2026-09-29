-- Prove2me | Theorems.Thm_MvFormalGroup_CartierModule_exists_forall_le_order_coeff_sub_and_frobIntPt_iterate_of_forall_le_order_presPi
-- name    : MvFormalGroup.CartierModule.exists_forall_le_order_coeff_sub_and_frobIntPt_iterate_of_forall_le_order_presPi
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.856965+00:00
-- url     : https://prove2.me/theorems/eb423a42-f1df-56bb-8455-1472f14a2f2d
-- title:
--   Cartier presentation: relations to every order over arbitrary base
-- statement:
--   Let $p$ be a prime, $R$ a commutative ring and $\Phi$ a commutative $d$-dimensional formal group law over $R$ (given by $d$ power series in two blocks of $d$ variables, with vanishing constant terms, linear coefficients $\delta_{ij}$ in each block, associativity and the commutation identity). Let $f : \mathrm{Fin}\,d \to$ `CartierModule p Φ`, each $f_i$ being a $d$-tuple of power series in countably many variables with zero constant terms satisfying the compatibility of Witt addition with $\Phi$, and assume the tangent data $\mathrm{tangent}(f_i)_j$, the coefficient of the first variable in the $j$-th component, equals $1$ if $i=j$ and $0$ otherwise. Let $w : \mathbb{N} \to \mathrm{Fin}\,d \to \mathrm{Fin}\,d \to W_p(R)$ and $h : \mathbb{N} \to \mathrm{Fin}\,d \to$ `CartierModule p Φ` satisfy, for every $N$ and $i$,
--   $$\mathrm{frobenius}(f_i) = \sum_{m<N} \mathrm{verschiebungInt}^{m}\Big(\sum_{l} w_{m,i,l}\cdot f_l\Big) + \mathrm{verschiebungInt}^{N}(h_{N,i}).$$
--   Let $\tau$ be a finite type, $n \in \mathbb{N}$, and $v : \mathrm{Fin}\,d \to$ `seriesPoint p R τ`, i.e. Witt vectors over $R[[\tau]]$ all of whose coefficients have zero constant term and form a substitutable family, such that every component of $\mathrm{presPi}\,f\,v = \sum_l \mathrm{evalPt}(f_l)(v_l)$ has order $\ge n$. Then there are $N \in \mathbb{N}$ and $u : \mathrm{Fin}\,d \to$ `seriesPoint p R τ` such that every Witt coefficient of $v_l - \big(\mathrm{verPt}(u_l) - \sum_i \sum_{m<N} w_{m,i,l}\cdot \mathrm{frobIntPt}^{m}(u_i)\big)$, for each $l$, and every Witt coefficient of $\mathrm{frobIntPt}^{N}(u_i)$, for each $i$, has order $\ge n$.
--
--   This is the exactness half of Cartier's second theorem in the form valid over an arbitrary base ring with $W_p(R)$-coefficients: a family of points of the formal Witt group killed by the presentation map $\Pi_f$ to order $n$ comes, to order $n$, from the standard relation module, at some finite level $N$ depending on the data. Off characteristic $p$ the integral Frobenius need not raise the $\tau$-adic order, which is why the level $N$ is existentially quantified and accompanied by the second conjunct; the statement feeds the construction of a homomorphism out of $\Phi$ in [`MvFormalGroup.CartierModule.exists_hom_forall_map_eq_of_forall_frobenius_eq_sum_verschiebungInt_iterate_smul`](thm.html#MvFormalGroup.CartierModule.exists_hom_forall_map_eq_of_forall_frobenius_eq_sum_verschiebungInt_iterate_smul).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MvFormalGroup_CartierModule_exists_forall_le_order_coeff_sub_and_frobIntPt_iterate_of_forall_le_order_presPi.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleHomothety
import Definitions.Def_MvFormalGroup_CartierModuleWittAction
import Definitions.Def_MvFormalGroup_CartierModuleIntVerschiebung
import Definitions.Def_MvFormalGroup_WittPointFamily
import Definitions.Def_MvFormalGroup_WittPointFamilyInt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

theorem MvFormalGroup.CartierModule.exists_forall_le_order_coeff_sub_and_frobIntPt_iterate_of_forall_le_order_presPi
    (p : ℕ) [Fact p.Prime] {R : Type u} [CommRing R] {d : ℕ}
    (Φ : MvFormalGroup d R) [Φ.IsComm]
    (f : Fin d → MvFormalGroup.CartierModule p Φ)
    (hf : ∀ i j, MvFormalGroup.CartierModule.tangent (f i) j = if i = j then 1 else 0)
    (w : ℕ → Fin d → Fin d → WittVector p R)
    (h : ℕ → Fin d → MvFormalGroup.CartierModule p Φ)
    (hexp : ∀ (N : ℕ) (i : Fin d), MvFormalGroup.CartierModule.frobenius (f i) =
      (∑ m ∈ Finset.range N, (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ)))^[m]
          (∑ l : Fin d, w m i l • f l)) +
        (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ)))^[N] (h N i))
    {τ : Type v} [Finite τ] (n : ℕ)
    (v : Fin d → MvFormalGroup.WittLaw.seriesPoint p R τ)
    (hv : ∀ j, (n : ℕ∞) ≤ ((MvFormalGroup.CartierModule.presPi f v).val j).order) :
    ∃ (N : ℕ) (u : Fin d → MvFormalGroup.WittLaw.seriesPoint p R τ),
      (∀ (l : Fin d) (k : ℕ), (n : ℕ∞) ≤
        ((v l : WittVector p (MvPowerSeries τ R)).coeff k -
          ((MvFormalGroup.WittLaw.verPt (u l) -
              ∑ i : Fin d, ∑ m ∈ Finset.range N, MvFormalGroup.WittLaw.wittSMulPt (w m i l)
                ((⇑(MvFormalGroup.WittLaw.frobIntPt (p := p) (R := R) (τ := τ)))^[m] (u i)) :
              MvFormalGroup.WittLaw.seriesPoint p R τ) : WittVector p (MvPowerSeries τ R)).coeff k).order) ∧
      (∀ (i : Fin d) (k : ℕ), (n : ℕ∞) ≤
        ((((⇑(MvFormalGroup.WittLaw.frobIntPt (p := p) (R := R) (τ := τ)))^[N] (u i) :
            MvFormalGroup.WittLaw.seriesPoint p R τ) : WittVector p (MvPowerSeries τ R)).coeff k).order) := by sorry
