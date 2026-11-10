-- Prove2me | Theorems.Thm_IntLInfty_Kan_cone_homotopy_operator
-- name    : IntLInfty.Kan.cone_homotopy_operator
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-10T03:10:39.919045+00:00
-- url     : https://prove2.me/theorems/41e91e5c-766a-42cb-9431-45cb737d9a35
-- title:
--   The cone homotopy operator on $C^r$ forms on the simplex: $dK+Kd=1$, $K^2=0$, face compatibility, and its continuous linear versions
-- statement:
--   Let $r\ge1$ and let $K$ be the cone (Poincar\'e) operator on forms on $\Delta^m$, $$(K_n\beta)(y)=\iota_y\int_0^1 t^n\,\beta(ty)\,dt,$$ given as any family `Kc` satisfying this formula. Then for $C^r$ forms: (1) if $\beta$ has degree $n+1$, $K_n\beta$ is a $C^r$ form of degree $n$ and $dK_n\beta+K_{n+1}d\beta=\beta$ on $\Delta^m$; (2) $K\circ K=0$; (3) $K\beta$ on $\Delta^m$ depends only on $\beta$ on $\Delta^m$; (4) $K$ is additive on $C^r$ forms and homogeneous; (5) pulling back along a face $\partial_i$ with $i\ne0$ commutes with $K$; (6) $d$ raises degree by one and preserves $C^r$; (7) coordinatewise, $K_n\beta(y)=\iota_y\sum_I\big(\int_0^1 s^n\beta_I(sy)\,ds\big)e_I$ on $\Delta^m$; (8) there are continuous linear maps $K:\Omega^{n+1}_{C^r}(\Delta^m)\to\Omega^n_{C^r}(\Delta^m)$ and $d:\Omega^n_{C^r}\to\Omega^{n+1}_{C^r}$ on the Banach spaces of $C^r$ jets, acting on jets of $C^r$ forms as $K$ and $d$, with $dK+Kd=1$, $KK=0$, $dd=0$, $(Kd)^2=Kd$, and commuting with the face maps (for $K$: faces $i\ne0$).
--
--   Role: the homotopy operator of the proof of Theorem 5.10 (the Volterra chart $H=Kd$ and the cone integrals).
-- source:
--   Henriques, Integrating L-infinity algebras, Compositio Math. 144 (2008), arXiv:math/0603563v2, https://arxiv.org/abs/math/0603563, proof of Theorem 5.10 (Section 5, pp. 15-17: the cone operator K with dK+Kd=1)

import Mathlib
import Definitions.Def_IntLInfty_Kan_Forms

theorem IntLInfty.Kan.cone_homotopy_operator (r : ℕ) (hr : 1 ≤ r)
    (Kc : ∀ m : ℕ, ℕ → IntLInfty.Kan.Ω m → IntLInfty.Kan.Ω m)
    (hKc : ∀ (m n : ℕ) (β : IntLInfty.Kan.Ω m) (y : Fin m → ℝ),
      letI : NormedAddCommGroup (ExteriorAlgebra ℝ (Module.Dual ℝ (Fin m → ℝ))) :=
        NormedAddCommGroup.induced (ExteriorAlgebra ℝ (Module.Dual ℝ (Fin m → ℝ)))
          (Finset (Fin m) → ℝ) (IntLInfty.Kan.formBasis m).equivFun.toLinearMap
          (IntLInfty.Kan.formBasis m).equivFun.injective
      letI : NormedSpace ℝ (ExteriorAlgebra ℝ (Module.Dual ℝ (Fin m → ℝ))) :=
        NormedSpace.induced ℝ (ExteriorAlgebra ℝ (Module.Dual ℝ (Fin m → ℝ)))
          (Finset (Fin m) → ℝ) (IntLInfty.Kan.formBasis m).equivFun.toLinearMap
      Kc m n β y = CliffordAlgebra.contractLeft (Module.Dual.eval ℝ (Fin m → ℝ) y)
        (∫ t in (0 : ℝ)..1, t ^ n • β (t • y))) :
    (∀ (m n : ℕ) (β : IntLInfty.Kan.Ω m), IntLInfty.Kan.IsCr r β → IntLInfty.Kan.IsDeg (n + 1) β →
      IntLInfty.Kan.IsDeg n (Kc m n β) ∧ IntLInfty.Kan.IsCr r (Kc m n β) ∧
      ∀ x ∈ IntLInfty.Kan.simplex m,
        IntLInfty.Kan.extD (Kc m n β) x + Kc m (n + 1) (IntLInfty.Kan.extD β) x = β x) ∧
    (∀ (m p n : ℕ) (β : IntLInfty.Kan.Ω m), Kc m p (Kc m n β) = 0) ∧
    (∀ (m n : ℕ) (β β' : IntLInfty.Kan.Ω m), (∀ x ∈ IntLInfty.Kan.simplex m, β x = β' x) →
      ∀ x ∈ IntLInfty.Kan.simplex m, Kc m n β x = Kc m n β' x) ∧
    (∀ (m n : ℕ) (β β' : IntLInfty.Kan.Ω m), IntLInfty.Kan.IsCr r β → IntLInfty.Kan.IsCr r β' →
      ∀ x ∈ IntLInfty.Kan.simplex m, Kc m n (β + β') x = Kc m n β x + Kc m n β' x) ∧
    (∀ (m n : ℕ) (c : ℝ) (β : IntLInfty.Kan.Ω m) (x : Fin m → ℝ), Kc m n (c • β) x = c • Kc m n β x) ∧
    (∀ (m n : ℕ) (i : Fin (m + 2)), i ≠ 0 → ∀ β : IntLInfty.Kan.Ω (m + 1), IntLInfty.Kan.IsCr r β →
      ∀ x ∈ IntLInfty.Kan.simplex m,
        IntLInfty.Kan.pull m i (Kc (m + 1) n β) x = Kc m n (IntLInfty.Kan.pull m i β) x) ∧
    (∀ (m n : ℕ) (ω : IntLInfty.Kan.Ω m), IntLInfty.Kan.IsCr r ω → IntLInfty.Kan.IsDeg n ω →
      IntLInfty.Kan.IsDeg (n + 1) (IntLInfty.Kan.extD ω)) ∧
    (∀ (m : ℕ) (ω : IntLInfty.Kan.Ω m), IntLInfty.Kan.IsCr r ω →
      IntLInfty.Kan.IsCr r (IntLInfty.Kan.extD ω)) ∧
    (∀ (m n : ℕ) (β : IntLInfty.Kan.Ω m), IntLInfty.Kan.IsCr r β → ∀ y ∈ IntLInfty.Kan.simplex m,
      Kc m n β y = CliffordAlgebra.contractLeft (Module.Dual.eval ℝ (Fin m → ℝ) y)
        (∑ I : Finset (Fin m), (∫ s in (0 : ℝ)..1, s ^ n * IntLInfty.Kan.coeff β I (s • y)) •
          IntLInfty.Kan.formBasis m I)) ∧
    ∃ (K : ∀ m n : ℕ, IntLInfty.Kan.CrForms r m (n + 1) →L[ℝ] IntLInfty.Kan.CrForms r m n)
      (d : ∀ m n : ℕ, IntLInfty.Kan.CrForms r m n →L[ℝ] IntLInfty.Kan.CrForms r m (n + 1)),
      (∀ (m n : ℕ) (w : IntLInfty.Kan.CrForms r m (n + 1)) (ω : IntLInfty.Kan.Ω m),
        IntLInfty.Kan.IsCr r ω → IntLInfty.Kan.jet r ω = w →
        (K m n w : IntLInfty.Kan.Jet r m × IntLInfty.Kan.Jet r m) = IntLInfty.Kan.jet r (Kc m n ω)) ∧
      (∀ (m n : ℕ) (w : IntLInfty.Kan.CrForms r m n) (ω : IntLInfty.Kan.Ω m),
        IntLInfty.Kan.IsCr r ω → IntLInfty.Kan.jet r ω = w →
        (d m n w : IntLInfty.Kan.Jet r m × IntLInfty.Kan.Jet r m) =
          IntLInfty.Kan.jet r (IntLInfty.Kan.extD ω)) ∧
      (∀ (m n : ℕ) (w : IntLInfty.Kan.CrForms r m (n + 1)),
        d m n (K m n w) + K m (n + 1) (d m (n + 1) w) = w) ∧
      (∀ (m n : ℕ) (w : IntLInfty.Kan.CrForms r m (n + 2)), K m n (K m (n + 1) w) = 0) ∧
      (∀ (m n : ℕ) (w : IntLInfty.Kan.CrForms r m n), d m (n + 1) (d m n w) = 0) ∧
      (∀ m n : ℕ, (K m n ∘L d m n) ∘L (K m n ∘L d m n) = K m n ∘L d m n) ∧
      (∀ (m n : ℕ) (i : Fin (m + 2)), i ≠ 0 → ∀ w : IntLInfty.Kan.CrForms r (m + 1) (n + 1),
        IntLInfty.Kan.faceCr r m n i (K (m + 1) n w) = K m n (IntLInfty.Kan.faceCr r m (n + 1) i w)) ∧
      (∀ (m n : ℕ) (i : Fin (m + 2)) (w : IntLInfty.Kan.CrForms r (m + 1) n),
        IntLInfty.Kan.faceCr r m (n + 1) i (d (m + 1) n w) = d m n (IntLInfty.Kan.faceCr r m n i w)) := by sorry
