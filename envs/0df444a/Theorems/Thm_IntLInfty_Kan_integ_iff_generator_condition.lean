-- Prove2me | Theorems.Thm_IntLInfty_Kan_integ_iff_generator_condition
-- name    : IntLInfty.Kan.integ_iff_generator_condition
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-10T03:10:37.618589+00:00
-- url     : https://prove2.me/theorems/0d20fac2-4607-434a-8f73-f8867fc873b1
-- title:
--   Integrality via generator values: smooth families and the cone condition
-- statement:
--   Facts about $C^\infty$ families of $C^r$ forms (closed under $0,+,\cdot,\sum,\wedge$, constants and change off the simplex), graded bookkeeping in $\Lambda^\bullet$, and, for any $C^r$ generator values $f$ representing $z\in\mathrm{Amb}_r(S,m)$ (vanishing in degrees $\ge m$) with algebra lift $\Phi$: smoothness of $z\mapsto\Phi_z(x)$, degree of $\Phi$ on $C^*(L)^p$, agreement on $\Delta^m$ of any DGA map representing $z$ with $f$, and $$z\in\int_S\iff K\big(d f(b_{t,k})-\Phi(\delta b_{t,k})\big)=0\ \text{on}\ \Delta^m\ \ \forall t,k$$ with $K$ the cone homotopy operator.
--
--   Role: step K0b of the proof of Theorem 5.10: integrality is the vanishing of the cone integral of the generator defects.
-- source:
--   Henriques, Integrating L-infinity algebras, Compositio Math. 144 (2008), arXiv:math/0603563v2, https://arxiv.org/abs/math/0603563, proof of Theorem 5.10 (Section 5, pp. 15-17)

import Mathlib
import Definitions.Def_IntLInfty_Kan_CE
import Definitions.Def_IntLInfty_Kan_Forms
import Definitions.Def_IntLInfty_Kan_Manifold
import Definitions.Def_IntLInfty_Kan_Integ

set_option autoImplicit false

open scoped ContDiff

namespace IntLInfty.Kan

theorem integ_iff_generator_condition :
    (∀ {m r : ℕ}, 1 ≤ r → ∀ {n : ℕ} {w0 : Ω m}, IsDeg n w0 ∧ IsCr r w0 → jet r w0 ∈ CrForms r m n) ∧
    (∀ {m r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E], 1 ≤ r → ∀ n : ℕ, (∃ a : E → CrForms r m n, ContDiff ℝ ∞ a ∧ ∀ z : E, (IsDeg n ((0 : Ω m)) ∧ IsCr r ((0 : Ω m))) ∧ jet r ((0 : Ω m)) = (a z : Jet r m × Jet r m))) ∧
    (∀ {m r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E], 1 ≤ r → ∀ {n : ℕ} {F G : E → Ω m}, (∃ a : E → CrForms r m n, ContDiff ℝ ∞ a ∧ ∀ z : E, (IsDeg n (F z) ∧ IsCr r (F z)) ∧ jet r (F z) = (a z : Jet r m × Jet r m)) → (∃ a : E → CrForms r m n, ContDiff ℝ ∞ a ∧ ∀ z : E, (IsDeg n (G z) ∧ IsCr r (G z)) ∧ jet r (G z) = (a z : Jet r m × Jet r m)) → (∃ a : E → CrForms r m n, ContDiff ℝ ∞ a ∧ ∀ z : E, (IsDeg n (F z + G z) ∧ IsCr r (F z + G z)) ∧ jet r (F z + G z) = (a z : Jet r m × Jet r m))) ∧
    (∀ {m r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E], 1 ≤ r → ∀ {n : ℕ} (c : ℝ) {F : E → Ω m}, (∃ a : E → CrForms r m n, ContDiff ℝ ∞ a ∧ ∀ z : E, (IsDeg n (F z) ∧ IsCr r (F z)) ∧ jet r (F z) = (a z : Jet r m × Jet r m)) → (∃ a : E → CrForms r m n, ContDiff ℝ ∞ a ∧ ∀ z : E, (IsDeg n (c • F z) ∧ IsCr r (c • F z)) ∧ jet r (c • F z) = (a z : Jet r m × Jet r m))) ∧
    (∀ {m r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E], 1 ≤ r → ∀ {n : ℕ} {ι : Type} (s : Finset ι) {F : ι → E → Ω m}, (∀ i ∈ s, (∃ a : E → CrForms r m n, ContDiff ℝ ∞ a ∧ ∀ z : E, (IsDeg n (F i z) ∧ IsCr r (F i z)) ∧ jet r (F i z) = (a z : Jet r m × Jet r m))) → (∃ a : E → CrForms r m n, ContDiff ℝ ∞ a ∧ ∀ z : E, (IsDeg n (∑ i ∈ s, F i z) ∧ IsCr r (∑ i ∈ s, F i z)) ∧ jet r (∑ i ∈ s, F i z) = (a z : Jet r m × Jet r m))) ∧
    (∀ {m r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E], 1 ≤ r → ∀ {p q : ℕ} {F G : E → Ω m}, (∃ a : E → CrForms r m p, ContDiff ℝ ∞ a ∧ ∀ z : E, (IsDeg p (F z) ∧ IsCr r (F z)) ∧ jet r (F z) = (a z : Jet r m × Jet r m)) → (∃ a : E → CrForms r m q, ContDiff ℝ ∞ a ∧ ∀ z : E, (IsDeg q (G z) ∧ IsCr r (G z)) ∧ jet r (G z) = (a z : Jet r m × Jet r m)) → (∃ a : E → CrForms r m (p + q), ContDiff ℝ ∞ a ∧ ∀ z : E, (IsDeg (p + q) (F z * G z) ∧ IsCr r (F z * G z)) ∧ jet r (F z * G z) = (a z : Jet r m × Jet r m))) ∧
    (∀ {m r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E], 1 ≤ r → ∀ {n : ℕ} {w0 : Ω m}, IsDeg n w0 ∧ IsCr r w0 → (∃ a : E → CrForms r m n, ContDiff ℝ ∞ a ∧ ∀ z : E, (IsDeg n (w0) ∧ IsCr r (w0)) ∧ jet r (w0) = (a z : Jet r m × Jet r m))) ∧
    (∀ {m r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ} {F G : E → Ω m}, (∃ a : E → CrForms r m n, ContDiff ℝ ∞ a ∧ ∀ z : E, (IsDeg n (F z) ∧ IsCr r (F z)) ∧ jet r (F z) = (a z : Jet r m × Jet r m)) → (∀ z, ∀ x ∈ simplex m, G z x = F z x) → (∃ a : E → CrForms r m n, ContDiff ℝ ∞ a ∧ ∀ z : E, (IsDeg n (G z) ∧ IsCr r (G z)) ∧ jet r (G z) = (a z : Jet r m × Jet r m))) ∧
    (∀ {m : ℕ} (c : ℝ), IsDeg 0 (algebraMap ℝ (Ω m) c)) ∧
    (∀ {m r : ℕ} (c : ℝ), IsCr r (algebraMap ℝ (Ω m) c)) ∧
    (∀ {m : ℕ} {ι : Type} [Fintype ι] (d : ι → ℕ) {n : ℕ}, ∀ y ∈ ⋀[ℝ]^n (Module.Dual ℝ (Fin m → ℝ)), ∀ g : ι → ExteriorAlgebra ℝ (Module.Dual ℝ (Fin m → ℝ)), (∀ i, g i ∈ ⋀[ℝ]^(d i) (Module.Dual ℝ (Fin m → ℝ))) → y = ∑ i, g i → y = ∑ i with d i = n, g i) ∧
    (∀ {m r : ℕ} {L : ℕ → Type} [∀ i, AddCommGroup (L i)] [∀ i, _root_.Module ℝ (L i)] [∀ i, FiniteDimensional ℝ (L i)] (S : GenSys L) (t : Fin m) (k : Fin (Module.finrank ℝ (S t))), ContDiff ℝ ∞ (fun z : Amb r S m => z t k)) ∧
    (∀ {V : Type} [AddCommGroup V] [_root_.Module ℝ V] [FiniteDimensional ℝ V] {p : ℕ}, Module.finrank ℝ V < p → ∀ {a : ExteriorAlgebra ℝ V}, a ∈ ⋀[ℝ]^p V → a = 0) ∧
    (∀ {m p : ℕ}, m < p → ∀ {a : ExteriorAlgebra ℝ (Module.Dual ℝ (Fin m → ℝ))}, a ∈ ⋀[ℝ]^p (Module.Dual ℝ (Fin m → ℝ)) → a = 0) ∧
    (∀ {m r : ℕ}, 1 ≤ r → ∀ {ι : Type} (s : Finset ι) (ϖ : ι → Ω m), (∀ k ∈ s, IsCr r (ϖ k)) → IsCr r (∑ k ∈ s, ϖ k)) ∧
    (∀ {m : ℕ} {L : ℕ → Type} [∀ i, AddCommGroup (L i)] [∀ i, _root_.Module ℝ (L i)] (f : ∀ i, Module.Dual ℝ (L i) →ₗ[ℝ] Ω m), (∀ (i : ℕ) (ξ : Module.Dual ℝ (L i)) (x : Fin m → ℝ), f i ξ x ∈ ⋀[ℝ]^(i + 1) (Module.Dual ℝ (Fin m → ℝ))) → ∀ Φ : CE L →ₐ[ℝ] Ω m, (∀ (i : ℕ) (ξ : Module.Dual ℝ (L i)), Φ (gen L i ξ) = f i ξ) → ∀ {p : ℕ} {c : CE L}, c ∈ ceDeg L p → ∀ x : Fin m → ℝ, Φ c x ∈ ⋀[ℝ]^p (Module.Dual ℝ (Fin m → ℝ))) ∧
    (∀ {m r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {L : ℕ → Type} [∀ i, AddCommGroup (L i)] [∀ i, _root_.Module ℝ (L i)], 1 ≤ r → ∀ (S : GenSys L) (f : E → ∀ i, Module.Dual ℝ (L i) →ₗ[ℝ] Ω m), (∀ (z : E) (i : ℕ) (ξ : Module.Dual ℝ (L i)) (x : Fin m → ℝ), f z i ξ x ∈ ⋀[ℝ]^(i + 1) (Module.Dual ℝ (Fin m → ℝ))) → ∀ Φ : E → CE L →ₐ[ℝ] Ω m, (∀ (z : E) (i : ℕ) (ξ : Module.Dual ℝ (L i)), Φ z (gen L i ξ) = f z i ξ) → (∀ (i : ℕ), ∀ ξ ∈ S i, (∃ a : E → CrForms r m (i + 1), ContDiff ℝ ∞ a ∧ ∀ z : E, (IsDeg (i + 1) (f z i ξ) ∧ IsCr r (f z i ξ)) ∧ jet r (f z i ξ) = (a z : Jet r m × Jet r m))) → ∀ {n : ℕ}, ∀ c ∈ genAlg L S, (∀ z, IsDeg n (Φ z c)) → (∃ a : E → CrForms r m n, ContDiff ℝ ∞ a ∧ ∀ z : E, (IsDeg n (Φ z c) ∧ IsCr r (Φ z c)) ∧ jet r (Φ z c) = (a z : Jet r m × Jet r m))) ∧
    (∀ {m r : ℕ} {L : ℕ → Type} [∀ i, AddCommGroup (L i)] [∀ i, _root_.Module ℝ (L i)] [∀ i, FiniteDimensional ℝ (L i)], 1 ≤ r → ∀ (δ : LInfty L) (S : GenSys L) (z : Amb r S m) (f : ∀ i, Module.Dual ℝ (L i) →ₗ[ℝ] Ω m), (∀ (i : ℕ) (ξ : Module.Dual ℝ (L i)), IsCr r (f i ξ)) → (∀ i : ℕ, m ≤ i → ∀ ξ : Module.Dual ℝ (L i), f i ξ = 0) → (∀ (t : Fin m) (k : Fin (Module.finrank ℝ (S t))), jet r (f t (genBasis S t k)) = (z t k : Jet r m × Jet r m)) → ∀ φ : genAlg L S →ₐ[ℝ] Ω m, IsDGAMap r δ S m φ → (∀ (t : Fin m) (k : Fin (Module.finrank ℝ (S t))), (z t k : Jet r m × Jet r m) = jet r (φ ⟨gen L t (genBasis S t k), gen_mem_genAlg S (genBasis S t k).2⟩)) → ∀ (i : ℕ) (ξ : Module.Dual ℝ (L i)) (hξ : ξ ∈ S i), ∀ x ∈ simplex m, φ ⟨gen L i ξ, gen_mem_genAlg S hξ⟩ x = f i ξ x) ∧
    (∀ {r : ℕ} {L : ℕ → Type} [∀ i, AddCommGroup (L i)] [∀ i, _root_.Module ℝ (L i)] [∀ i, FiniteDimensional ℝ (L i)], 1 ≤ r → ∀ (Kc : ∀ m : ℕ, ℕ → Ω m → Ω m),
      (∀ (m n : ℕ) (β : Ω m) (y : Fin m → ℝ),
        letI : NormedAddCommGroup (ExteriorAlgebra ℝ (Module.Dual ℝ (Fin m → ℝ))) :=
          NormedAddCommGroup.induced (ExteriorAlgebra ℝ (Module.Dual ℝ (Fin m → ℝ)))
            (Finset (Fin m) → ℝ) (formBasis m).equivFun.toLinearMap (formBasis m).equivFun.injective
        letI : NormedSpace ℝ (ExteriorAlgebra ℝ (Module.Dual ℝ (Fin m → ℝ))) :=
          NormedSpace.induced ℝ (ExteriorAlgebra ℝ (Module.Dual ℝ (Fin m → ℝ)))
            (Finset (Fin m) → ℝ) (formBasis m).equivFun.toLinearMap
        Kc m n β y = CliffordAlgebra.contractLeft (Module.Dual.eval ℝ (Fin m → ℝ) y)
          (∫ t in (0 : ℝ)..1, t ^ n • β (t • y))) → ∀ (δ : LInfty L) (S : GenSys L), (∀ (i : ℕ) (ξ : Module.Dual ℝ (L i)), ξ ∈ S i → δ.δ (gen L i ξ) ∈ genAlg L S) → ∀ {m : ℕ} (z : Amb r S m) (f : ∀ i, Module.Dual ℝ (L i) →ₗ[ℝ] Ω m), (∀ (i : ℕ) (ξ : Module.Dual ℝ (L i)) (x : Fin m → ℝ), f i ξ x ∈ ⋀[ℝ]^(i + 1) (Module.Dual ℝ (Fin m → ℝ))) → (∀ (i : ℕ) (ξ : Module.Dual ℝ (L i)), IsCr r (f i ξ)) → (∀ i : ℕ, m ≤ i → ∀ ξ : Module.Dual ℝ (L i), f i ξ = 0) → (∀ (t : Fin m) (k : Fin (Module.finrank ℝ (S t))), jet r (f t (genBasis S t k)) = (z t k : Jet r m × Jet r m)) → ∀ Φ : CE L →ₐ[ℝ] Ω m, (∀ (i : ℕ) (ξ : Module.Dual ℝ (L i)), Φ (gen L i ξ) = f i ξ) → (z ∈ integ r δ S m ↔ ∀ j : (t : Fin m) × Fin (Module.finrank ℝ (S t)), ∀ x ∈ simplex m, Kc m ((j.1 : ℕ) + 1) (extD (f j.1 (genBasis S j.1 j.2)) - Φ (δ.δ (gen L j.1 (genBasis S j.1 j.2)))) x = 0)) := by sorry

end IntLInfty.Kan
