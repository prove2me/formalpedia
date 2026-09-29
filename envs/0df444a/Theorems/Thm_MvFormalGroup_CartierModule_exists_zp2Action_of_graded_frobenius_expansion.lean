-- Prove2me | Theorems.Thm_MvFormalGroup_CartierModule_exists_zp2Action_of_graded_frobenius_expansion
-- name    : MvFormalGroup.CartierModule.exists_zp2Action_of_graded_frobenius_expansion
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.856965+00:00
-- url     : https://prove2.me/theorems/7152b43d-3d16-55b7-a5b9-1846cdc3611c
-- title:
--   Graded Frobenius expansion yields a ℤ_{p²}-action on Φ
-- statement:
--   Let $p$ be a prime and $B$ a commutative $\mathbb{Z}_p$-algebra equipped with a ring homomorphism $j\colon \mathbb{Z}_{p^2}=W(\mathbb{F}_{p^2})\to B$, where $\mathbb{F}_{p^2}$ is `GaloisField p 2`. Let $\Phi$ be a commutative formal group law of dimension $2$ over $B$, and let $f_0,f_1$ be elements of its Cartier module with standard tangent vectors, $\mathrm{tangent}(f_i)_l=\delta_{il}$. Suppose given coefficients $c_{m,i,l}\in B$ vanishing whenever $l\not\equiv m+i+1 \pmod 2$, and elements $h_{N,i}$ of the Cartier module, such that for every $N$ and every $i$ one has the expansion $F f_i=\sum_{m<N}V^m\bigl(\sum_l \langle c_{m,i,l}\rangle f_l\bigr)+V^N h_{N,i}$, with $F$ the Frobenius, $V$ the operator `verschiebungInt` and $\langle\cdot\rangle$ the homothety operators on the Cartier module. Then there exist a ring homomorphism $\theta\colon\mathbb{Z}_{p^2}\to W(\mathbb{Z}_{p^2})$ and a map $a\mapsto \mathrm{act}(a)$ from $\mathbb{Z}_{p^2}$ to pairs of power series in two variables over $B$, each $\mathrm{act}(a)$ satisfying `IsLawHom Φ Φ` (vanishing constant coefficients and the endomorphism substitution identity), such that: the ghost components satisfy $\mathrm{gh}_n(\theta a)=\sigma^n(a)$ for $\sigma$ the Witt vector Frobenius of $\mathbb{Z}_{p^2}$; $\theta$ takes Teichmüller representatives of $\mathbb{F}_{p^2}$ to iterated Teichmüller representatives; $\mathrm{act}(1)$ is the identity series; $\mathrm{act}(ab)$ is the substitution of $\mathrm{act}(b)$ into $\mathrm{act}(a)$; $\mathrm{act}(a+b)$ is the $\Phi$-sum of $\mathrm{act}(a)$ and $\mathrm{act}(b)$; and the induced endomorphism of the Cartier module sends $f_i$ to $W(j)\bigl(\theta(\sigma^i a)\bigr)\cdot f_i$ for $i=0,1$.
--
--   This is the formal-group-law form of the equivalence, in Boutot–Carayol's treatment of the Čerednik–Drinfeld uniformisation, between a $\mathbb{Z}/2$-graded $V$-basis of the Cartier module and an action of the unramified quadratic ring $\mathbb{Z}_{p^2}$ on the law. It is used in the construction of homogeneous $V$-bases with structure constants for formal $\mathcal{O}_D$-modules, via [`CerednikDrinfeld.FormalODModule.exists_isHomogeneousVBasis_and_hasStructureConstants_liftVar`](thm.html#CerednikDrinfeld.FormalODModule.exists_isHomogeneousVBasis_and_hasStructureConstants_liftVar).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MvFormalGroup_CartierModule_exists_zp2Action_of_graded_frobenius_expansion.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleHomothety
import Definitions.Def_MvFormalGroup_CartierModuleWittAction
import Definitions.Def_MvFormalGroup_CartierModuleIntVerschiebung
import Definitions.Def_MvFormalGroup_CartierModuleBaseChange
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_CartierGradedPiece
import Definitions.Def_CerednikDrinfeld_CartierStructureConstants

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem MvFormalGroup.CartierModule.exists_zp2Action_of_graded_frobenius_expansion
    (p : ℕ) [Fact p.Prime] {B : Type u} [CommRing B] [Algebra (PadicInt p) B]
    (j : CerednikDrinfeld.Zp2 p →+* B)
    (Φ : MvFormalGroup 2 B) [Φ.IsComm]
    (f : Fin 2 → MvFormalGroup.CartierModule p Φ)
    (hf : ∀ i l, MvFormalGroup.CartierModule.tangent (f i) l = if i = l then 1 else 0)
    (c : ℕ → Fin 2 → Fin 2 → B)
    (hc : ∀ (m : ℕ) (i l : Fin 2), (l : ℕ) ≠ (m + i + 1) % 2 → c m i l = 0)
    (h : ℕ → Fin 2 → MvFormalGroup.CartierModule p Φ)
    (hexp : ∀ (N : ℕ) (i : Fin 2), MvFormalGroup.CartierModule.frobenius (f i) =
      (∑ m ∈ Finset.range N, (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ)))^[m]
          (∑ l : Fin 2, MvFormalGroup.CartierModule.homothety (c m i l) (f l))) +
        (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ)))^[N] (h N i)) :
    ∃ (θ : CerednikDrinfeld.Zp2 p →+* WittVector p (CerednikDrinfeld.Zp2 p))
      (act : CerednikDrinfeld.Zp2 p → CerednikDrinfeld.SpecialFormal.Series B)
      (hact : ∀ a, CerednikDrinfeld.SpecialFormal.IsLawHom Φ Φ (act a)),
      (∀ (a : CerednikDrinfeld.Zp2 p) (n : ℕ), WittVector.ghostComponent n (θ a) =
          (⇑(WittVector.frobenius (p := p) (R := GaloisField p 2)))^[n] a) ∧
      (∀ c : GaloisField p 2, θ (WittVector.teichmuller p c) =
          WittVector.teichmuller p (WittVector.teichmuller p c)) ∧
      act 1 = CerednikDrinfeld.SpecialFormal.Series.id B ∧
      (∀ a b, act (a * b) = (act a).comp (act b)) ∧
      (∀ a b, act (a + b) = CerednikDrinfeld.SpecialFormal.Series.addVia Φ (act a) (act b)) ∧
      ∀ (a : CerednikDrinfeld.Zp2 p) (i : Fin 2),
        MvFormalGroup.CartierModule.map (hact a).toHom (f i) =
          WittVector.map j (θ ((⇑(WittVector.frobenius (p := p) (R := GaloisField p 2)))^[(i : ℕ)] a)) • f i := by sorry
