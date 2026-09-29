-- Prove2me | Theorems.Thm_NumberField_TateGlobal_exists_forall_exists_isIdeleClassChar_isUnramifiedCharAt_archLocalChar_eq_abs_sub_le
-- name    : NumberField.TateGlobal.exists_forall_exists_isIdeleClassChar_isUnramifiedCharAt_archLocalChar_eq_abs_sub_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.351487+00:00
-- url     : https://prove2.me/theorems/78dfcc93-b869-5c95-815e-c930b584ea16
-- title:
--   Unramified unitary Hecke characters of nearly prescribed archimedean type
-- statement:
--   Let $K$ be a number field, with ring of integers $\mathcal O_K$ and adele ring $\mathbb A_K$. The assertion is that there is a real constant $B \ge 0$ such that for every family of real numbers $\sigma = (\sigma_v)$ and every family of integers $b = (b_v)$ indexed by the infinite places of $K$, there exist a group homomorphism $\eta : \mathbb A_K^\times \to \mathbb C^\times$, a family of real numbers $\tau = (\tau_v)$ and a family of integers $m = (m_v)$, again indexed by the infinite places, with the following properties. First, $\eta$ is unitary, i.e. $\lvert \eta(x)\rvert = 1$ for every idele unit $x$; it is an idele class character, i.e. $\eta$ is trivial on the image of $K^\times$ under $\mathrm{Units.map}$ of the structure map $K \to \mathbb A_K$; and it is continuous. Second, $\eta$ is unramified at every finite place $v$ of $K$ (a height-one prime of $\mathcal O_K$), in the sense that the local character $\eta \circ \mathrm{finIncl} \circ \mathrm{localUnit}$ at $v$ takes the value $1$ on every unit $t$ of the completion $K_v$ such that both $t$ and $t^{-1}$ lie in the valuation ring $\mathcal O_v$. Third, for each infinite place $v$ the archimedean local character $x \mapsto \eta(\mathrm{archUnitHom}\,v\,x)$, obtained by sending $x \in K_v^\times$ to the idele with component $x$ at $v$, component $1$ at the other infinite places and finite part $1$, satisfies: if the canonical embedding $e_v : K_v \to \mathbb C$ sends $x$ to a number with positive real part and vanishing imaginary part, then $\eta(\mathrm{archUnitHom}\,v\,x)$ equals the $i\tau_v$-th complex power of the idele norm $\lVert \mathrm{archUnitHom}\,v\,x\rVert$ (the value of the distributive Haar character of $\mathbb A_K$ at that idele); and if $\lvert e_v(x)\rvert = 1$ then $\eta(\mathrm{archUnitHom}\,v\,x) = e_v(x)^{m_v}$. Finally $m_v = 0$ at every real place $v$, $\lvert \tau_v - \sigma_v\rvert \le B$ at every infinite place, $\lvert m_v - b_v\rvert \le B$ at every complex place, and $\sum_v \mathrm{mult}(v)\,(\tau_v - \sigma_v) = 0$, the sum being over all infinite places with $\mathrm{mult}(v) = [K_v : \mathbb R]$.
--
--   This is the existence half of Hecke's description of the Größencharaktere of a number field, in the quantitative form asserting that every prescribed archimedean type is approximated, to within a constant depending only on $K$, by the archimedean type of an everywhere unramified unitary idele class character, with exactness in the direction of the idele norm. It is used in the construction of auxiliary unramified characters entering the global Tate zeta integral part of the development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_TateGlobal_exists_forall_exists_isIdeleClassChar_isUnramifiedCharAt_archLocalChar_eq_abs_sub_le.lean

import Definitions.Def_NumberField_TateGlobalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain AutomorphicForm

theorem NumberField.TateGlobal.exists_forall_exists_isIdeleClassChar_isUnramifiedCharAt_archLocalChar_eq_abs_sub_le
    (K : Type) [Field K] [NumberField K] :
    ∃ B : ℝ, 0 ≤ B ∧
    ∀ (σ : InfinitePlace K → ℝ) (b : InfinitePlace K → ℤ),
    ∃ (η : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (τ : InfinitePlace K → ℝ) (m : InfinitePlace K → ℤ),
      IsUnitaryChar (𝓞 K) K η ∧ IsIdeleClassChar (𝓞 K) K η ∧ Continuous η ∧
      (∀ v : HeightOneSpectrum (𝓞 K), NumberField.TateGlobal.IsUnramifiedCharAt η v) ∧
      (∀ (v : InfinitePlace K) (x : (v.Completion)ˣ),
        0 < (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).re →
        (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).im = 0 →
        ((NumberField.TateGlobal.archLocalChar η v x : ℂˣ) : ℂ) =
          (((NumberField.TateGlobal.ideleNorm K (NumberField.TateGlobal.archUnitHom v x)) : ℝ) : ℂ) ^
            (((τ v : ℝ) : ℂ) * Complex.I)) ∧
      (∀ (v : InfinitePlace K) (x : (v.Completion)ˣ),
        ‖InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)‖ = 1 →
        ((NumberField.TateGlobal.archLocalChar η v x : ℂˣ) : ℂ) =
          (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)) ^ (m v)) ∧
      (∀ v : InfinitePlace K, v.IsReal → m v = 0) ∧
      (∀ v : InfinitePlace K, |τ v - σ v| ≤ B) ∧
      (∀ v : InfinitePlace K, v.IsComplex → (|m v - b v| : ℝ) ≤ B) ∧
      ∑ v : InfinitePlace K, (v.mult : ℝ) * (τ v - σ v) = 0 := by sorry
