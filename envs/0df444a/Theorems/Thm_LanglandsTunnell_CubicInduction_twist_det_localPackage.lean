-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_twist_det_localPackage
-- name    : LanglandsTunnell.CubicInduction.twist_det_localPackage
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.012626+00:00
-- url     : https://prove2.me/theorems/4d38de91-c616-52ba-8913-844f6c1eed78
-- title:
--   Twisting a local GL₃ package by χᵥ ∘ det
-- statement:
--   Let $v$ be a height-one prime of $\mathcal O_{\mathbb Q}$ and write $\mathbb Q_v$ for the $v$-adic completion and `LocalGL3 v` $= \mathrm{GL}_3(\mathbb Q_v)$. Fix an additive character $\psi_v$ of $\mathbb Q_v$ with values in $\mathbb C$, a homomorphism $\chi_v \colon \mathbb Q_v^\times \to \mathbb C^\times$, an open subgroup $U_0 \le \mathbb Q_v^\times$ on which $\chi_v$ is trivial, the unitarity hypothesis $\lvert \chi_v(z)\rvert = 1$ for all $z$, and a function $W \colon \mathrm{GL}_3(\mathbb Q_v) \to \mathbb C$; put $W^{\chi}(x) = \chi_v(\det x)\,W(x)$. Here `gl3CyclicSubspace W` is the $\mathbb C$-span of the right translates $h \mapsto W(h g)$ of $W$. The conclusion is a fourfold conjunction. (a) If for every open subgroup $U_v \le \mathrm{GL}_3(\mathbb Q_v)$ there is a finite set $B$ of functions such that every element of `gl3CyclicSubspace W` invariant under right translation by $U_v$ lies in the $\mathbb C$-span of $B$, then the same holds with $W$ replaced by $W^{\chi}$. (b) If `HasWhittakerMultOne ψv W` holds, i.e. the space `gl3WhittakerFunctionalSpace` of $\psi_v$-Whittaker functionals for the right-translation representation `gl3CyclicRep W` on `gl3CyclicSubspace W` has $\mathbb C$-rank at most $1$, then the same holds for $W^{\chi}$. (c) If some open subgroup of $\mathrm{GL}_3(\mathbb Q_v)$ fixes $W$ under right translation, then some open subgroup fixes $W^{\chi}$. (d) For every homomorphism $\omega_v \colon \mathbb Q_v^\times \to \mathbb C^\times$ with $\lvert \omega_v(z)\rvert = 1$ for all $z$ and $W(t \cdot 1_3 \, h) = \omega_v(t) W(h)$ for all $t$ and $h$, the character $\omega_v \chi_v^3$ is again unitary and $W^{\chi}(t \cdot 1_3\, h) = (\omega_v \chi_v^3)(t)\, W^{\chi}(h)$.
--
--   This is the local compatibility package for twisting a $\mathrm{GL}_3$ vector by a character of the determinant: admissibility of the cyclic space, multiplicity one for $\psi_v$-Whittaker functionals, smoothness (existence of an open right stabiliser) and the central character law all transfer from $W$ to $\chi_v(\det\,\cdot\,)W$, the central character changing by $\chi_v^3$. It is used in the twisted $\mathrm{GL}_3$ strand of the cubic base-change argument, in particular by [`LanglandsTunnell.CubicInduction.isCubicInductionDataOn_twist_det`](thm.html#LanglandsTunnell.CubicInduction.isCubicInductionDataOn_twist_det) and by the local zeta-integral statements for twisted cubic induction data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_twist_det_localPackage.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction

theorem LanglandsTunnell.CubicInduction.twist_det_localPackage
    (v : HeightOneSpectrum (𝓞 ℚ)) (ψv : AddChar (v.adicCompletion ℚ) ℂ)
    (χv : (v.adicCompletion ℚ)ˣ →* ℂˣ)
    (U₀ : Subgroup (v.adicCompletion ℚ)ˣ) (hU₀ : IsOpen (U₀ : Set (v.adicCompletion ℚ)ˣ)) (hχU₀ : ∀ u ∈ U₀, χv u = 1)
    (hχu : ∀ z : (v.adicCompletion ℚ)ˣ, ‖((χv z : ℂˣ) : ℂ)‖ = 1)
    (W : LocalGL3 v → ℂ) :

    ((∀ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) →
        ∃ B : Finset (LocalGL3 v → ℂ), ∀ G ∈ gl3CyclicSubspace W,
          (∀ k ∈ Uv, ∀ g : LocalGL3 v, G (g * k) = G g) → G ∈ Submodule.span ℂ (B : Set (LocalGL3 v → ℂ))) →
      ∀ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) →
        ∃ B : Finset (LocalGL3 v → ℂ), ∀ G ∈ gl3CyclicSubspace
            (fun x : LocalGL3 v => ((χv (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) * W x),
          (∀ k ∈ Uv, ∀ g : LocalGL3 v, G (g * k) = G g) → G ∈ Submodule.span ℂ (B : Set (LocalGL3 v → ℂ))) ∧

    (HasWhittakerMultOne ψv W →
      HasWhittakerMultOne ψv (fun x : LocalGL3 v => ((χv (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) * W x)) ∧

    ((∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧ ∀ k ∈ Uv, ∀ g : LocalGL3 v, W (g * k) = W g) →
      ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
        ∀ k ∈ Uv, ∀ g : LocalGL3 v,
          (fun x : LocalGL3 v => ((χv (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) * W x) (g * k) =
            (fun x : LocalGL3 v => ((χv (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) * W x) g) ∧

    (∀ ωv : (v.adicCompletion ℚ)ˣ →* ℂˣ, (∀ z : (v.adicCompletion ℚ)ˣ, ‖((ωv z : ℂˣ) : ℂ)‖ = 1) →
      (∀ (t : (v.adicCompletion ℚ)ˣ) (h : LocalGL3 v),
          W (Matrix.GeneralLinearGroup.scalar (Fin 3) t * h) = ((ωv t : ℂˣ) : ℂ) * W h) →
      (∀ z : (v.adicCompletion ℚ)ˣ, ‖(((ωv * χv ^ 3) z : ℂˣ) : ℂ)‖ = 1) ∧
      ∀ (t : (v.adicCompletion ℚ)ˣ) (h : LocalGL3 v),
        (fun x : LocalGL3 v => ((χv (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) * W x)
            (Matrix.GeneralLinearGroup.scalar (Fin 3) t * h) =
          (((ωv * χv ^ 3) t : ℂˣ) : ℂ) *
            (fun x : LocalGL3 v => ((χv (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) * W x) h) := by sorry
