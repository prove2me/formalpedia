-- Prove2me | Theorems.Thm_IntLInfty_Kan_crForms_exterior_calculus
-- name    : IntLInfty.Kan.crForms_exterior_calculus
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-10T03:10:36.623362+00:00
-- url     : https://prove2.me/theorems/360288f3-0c68-4400-a514-86c9ccf2ca67
-- title:
--   Exterior calculus of $C^r$ forms on the simplex: linearity, $d^2=0$, pullback along cofaces, and face maps on jets
-- statement:
--   For forms on the simplex $\Delta^m$ (coefficients in the basis $dx_I$, exterior derivative $d$ computed with derivatives within $\Delta^m$), with $r\ge1$ where needed:
--   $$d(\omega+\omega')=d\omega+d\omega',\quad d(c\,\omega)=c\,d\omega,\quad d(d\omega)=0,\quad d(\partial_i^*\omega)=\partial_i^*(d\omega),\quad d_i\,[j^r\omega]=j^r(\partial_i^*\omega)$$
--   for $C^r$ forms $\omega,\omega'$ (so $C^r$ forms, closed forms and forms of degree $n$ are linear subspaces, stable under the coface pullbacks $\partial_i^*$); the jet map $j^r$ is linear on $C^r$ forms, depends only on the values on $\Delta^m$ and determines them; the operator $\mathrm{viaRep}$ (hence $d_i$ on $\Omega_{C^r}$ and $\Omega_{\mathrm{closed}}$ and $d$ on jets) is computed by any representative; plus the elementary facts used with these: $\Delta^m$ is convex, closed, has unique derivatives within it, contains its vertices and is mapped into $\Delta^{m+1}$ by every coface; jet components are continuous and evaluate to iterated derivatives within $\Delta^m$; exterior powers are preserved by $\Lambda f$; naturality of $\sum_a dx_a\wedge T(e_a)$ under linear maps.
--
--   Role: the clean calculus lemmas every later step of the proof of Theorem 5.10 uses on forms.
-- source:
--   Henriques, Integrating L-infinity algebras, arXiv:math/0603563v2, https://arxiv.org/abs/math/0603563, Convention 5.1 and Section 5 (Banach spaces of C^r forms on the simplex used in the proof of Theorem 5.10, p. 16)

import Mathlib
import Definitions.Def_IntLInfty_Kan_Forms

namespace IntLInfty.Kan

theorem crForms_exterior_calculus :
    (∀ (m : ℕ), Convex ℝ (simplex m)) ∧
    (∀ (m : ℕ), UniqueDiffOn ℝ (simplex m)) ∧
    (∀ {m : ℕ} (ω ω' : Ω m) (I : Finset (Fin m)),
      coeff (ω + ω') I = coeff ω I + coeff ω' I) ∧
    (∀ {m : ℕ} (c : ℝ) (ω : Ω m) (I : Finset (Fin m)),
      coeff (c • ω) I = c • coeff ω I) ∧
    (∀ {m r : ℕ} (hr : 1 ≤ r) {ω ω' : Ω m} (hω : IsCr r ω) (hω' : IsCr r ω') {x : Fin m → ℝ}
      (hx : x ∈ simplex m), extD (ω + ω') x = extD ω x + extD ω' x) ∧
    (∀ {m r : ℕ} (hr : 1 ≤ r) (c : ℝ) {ω : Ω m} (hω : IsCr r ω) {x : Fin m → ℝ}
      (hx : x ∈ simplex m), extD (c • ω) x = c • extD ω x) ∧
    (∀ {m : ℕ} {n : ℕ} {ω ω' : Ω m} (h : IsDeg n ω) (h' : IsDeg n ω'), IsDeg n (ω + ω')) ∧
    (∀ {m : ℕ} {n : ℕ} (c : ℝ) {ω : Ω m} (h : IsDeg n ω), IsDeg n (c • ω)) ∧
    (∀ {m r : ℕ} (hr : 1 ≤ r) {ω ω' : Ω m} (hω : IsCr r ω) (hω' : IsCr r ω'), IsCr r (ω + ω')) ∧
    (∀ {m r : ℕ} (hr : 1 ≤ r) (c : ℝ) {ω : Ω m} (hω : IsCr r ω), IsCr r (c • ω)) ∧
    (∀ {m r : ℕ} (hr : 1 ≤ r) {ω ω' : Ω m} (hω : IsCr r ω) (hω' : IsCr r ω'),
      jet r (ω + ω') = jet r ω + jet r ω') ∧
    (∀ {m r : ℕ} (hr : 1 ≤ r) (c : ℝ) {ω : Ω m} (hω : IsCr r ω),
      jet r (c • ω) = c • jet r ω) ∧
    (∀ {m r : ℕ}, IsCr r (0 : Ω m)) ∧
    (∀ {m : ℕ} {n : ℕ}, IsDeg n (0 : Ω m)) ∧
    (∀ (m : ℕ), IsClosed (simplex m)) ∧
    (∀ {m r : ℕ} {f : (Fin m → ℝ) → ℝ} (hf : ContDiffOn ℝ r f (simplex m)) {k : ℕ}
      (hk : k ≤ r) (β : Fin k → Fin m) {x : Fin m → ℝ} (hx : x ∈ simplex m),
      jetComp f k β ⟨x, hx⟩ = iteratedFDerivWithin ℝ k f (simplex m) x (fun l => Pi.single (β l) 1)) ∧
    (∀ {m r : ℕ} {f : (Fin m → ℝ) → ℝ} (hf : ContDiffOn ℝ r f (simplex m)) {k : ℕ}
      (hk : k = 0) (β : Fin k → Fin m) {x : Fin m → ℝ} (hx : x ∈ simplex m),
      jetComp f k β ⟨x, hx⟩ = f x) ∧
    (∀ {r m : ℕ} (I : Finset (Fin m)) (j : Fin (r + 1))
      (β : Fin (j : ℕ) → Fin m), Continuous (fun w : Jet r m => w I j β)) ∧
    (∀ {m r : ℕ} (hr : 1 ≤ r) {ω : Ω m} (hC : IsCr r ω), IsClosedForm (extD ω)) ∧
    (∀ {m r : ℕ} (hr : 1 ≤ r) {ω ω' : Ω m} (hω : IsCr r ω) (hω' : IsCr r ω')
      (h : IsClosedForm ω) (h' : IsClosedForm ω'), IsClosedForm (ω + ω')) ∧
    (∀ {m r : ℕ} (hr : 1 ≤ r) (c : ℝ) {ω : Ω m} (hω : IsCr r ω)
      (h : IsClosedForm ω), IsClosedForm (c • ω)) ∧
    (∀ {m : ℕ}, IsClosedForm (0 : Ω m)) ∧
    (∀ {m : ℕ} {ω ω' : Ω m} (h : ∀ x ∈ simplex m, ω x = ω' x) (I : Finset (Fin m)),
      Set.EqOn (coeff ω I) (coeff ω' I) (simplex m)) ∧
    (∀ {m : ℕ} {ω ω' : Ω m} (h : ∀ x ∈ simplex m, ω x = ω' x),
      ∀ x ∈ simplex m, extD ω x = extD ω' x) ∧
    (∀ {m r : ℕ} {ω ω' : Ω m} (h : ∀ x ∈ simplex m, ω x = ω' x), jet r ω = jet r ω') ∧
    (∀ {m r : ℕ} {ω ω' : Ω m} (hω : IsCr r ω) (hω' : IsCr r ω')
      (h : jet r ω = jet r ω'), ∀ x ∈ simplex m, ω x = ω' x) ∧
    (∀ (m : ℕ) (j : Fin (m + 1)), vertex m j ∈ simplex m) ∧
    (∀ {m : ℕ} (i : Fin (m + 2)) {x : Fin m → ℝ} (hx : x ∈ simplex m),
      coface m i x ∈ simplex (m + 1)) ∧
    (∀ {m r : ℕ} {m' n : ℕ} {V : Submodule ℝ (Jet r m' × Jet r m')} {F : Ω m → Ω m'}
      (hF : ∀ ω ω' : Ω m, (∀ x ∈ simplex m, ω x = ω' x) → ∀ x ∈ simplex m', F ω x = F ω' x)
      {ω : Ω m} (hD : IsDeg n ω) (hC : IsCr r ω) (hV : jet r (F ω) ∈ V),
      (viaRep n V F (jet r ω) : Jet r m' × Jet r m') = jet r (F ω)) ∧
    (∀ {m r : ℕ} {n : ℕ} {ω : Ω m} (hD : IsDeg n ω) (hC : IsCr r ω)
      (hw : jet r ω ∈ CrForms r m n) (hV : jet r (extD ω) ∈ CrClosed r m (n + 1)),
      (dCr r m n ⟨jet r ω, hw⟩ : Jet r m × Jet r m) = jet r (extD ω)) ∧
    (∀ {M N : Type} [AddCommGroup M] [Module ℝ M] [AddCommGroup N]
      [Module ℝ N] (f : M →ₗ[ℝ] N) {n : ℕ} {a : ExteriorAlgebra ℝ M} (ha : a ∈ ⋀[ℝ]^n M),
      ExteriorAlgebra.map f a ∈ ⋀[ℝ]^n N) ∧
    (∀ {m : ℕ} {n : ℕ} (i : Fin (m + 2)) {ω : Ω (m + 1)} (h : IsDeg n ω),
      IsDeg n (pull m i ω)) ∧
    (∀ {m' : ℕ} {A : Type} [AddCommGroup A] [Module ℝ A]
      (T : (Fin m' → ℝ) →ₗ[ℝ] A) (v : Fin m' → ℝ), T v = ∑ a, v a • T (Pi.single a 1)) ∧
    (∀ {m : ℕ} {m' : ℕ} (L : (Fin m → ℝ) →ₗ[ℝ] (Fin m' → ℝ))
      (T : (Fin m' → ℝ) →ₗ[ℝ] ExteriorAlgebra ℝ (Module.Dual ℝ (Fin m' → ℝ))),
      ExteriorAlgebra.map L.dualMap (∑ a, dx m' a * T (Pi.single a 1)) =
        ∑ k, dx m k * ExteriorAlgebra.map L.dualMap (T (L (Pi.single k 1)))) ∧
    (∀ {m r : ℕ} (hr : 1 ≤ r) (i : Fin (m + 2)) {ω : Ω (m + 1)}
      (hC : ∀ I, ContDiffOn ℝ r (coeff ω I) (simplex (m + 1))) {x : Fin m → ℝ}
      (hx : x ∈ simplex m), extD (pull m i ω) x = pull m i (extD ω) x) ∧
    (∀ {m r : ℕ} (hr : 1 ≤ r) (i : Fin (m + 2)) {ω : Ω (m + 1)} (hC : IsCr r ω),
      IsCr r (pull m i ω)) ∧
    (∀ {m r : ℕ} (hr : 1 ≤ r) (i : Fin (m + 2)) {ω : Ω (m + 1)} (hC : IsCr r ω)
      (h : IsClosedForm ω), IsClosedForm (pull m i ω)) ∧
    (∀ {m r : ℕ} {n : ℕ} (hr : 1 ≤ r) (i : Fin (m + 2)) {ω : Ω (m + 1)} (hD : IsDeg n ω)
      (hC : IsCr r ω) (hw : jet r ω ∈ CrForms r (m + 1) n),
      (faceCr r m n i ⟨jet r ω, hw⟩ : Jet r m × Jet r m) = jet r (pull m i ω)) ∧
    (∀ {m r : ℕ} {n : ℕ} (hr : 1 ≤ r) (i : Fin (m + 2)) {ω : Ω (m + 1)} (hD : IsDeg n ω)
      (hC : IsCr r ω) (hcl : IsClosedForm ω) (hw : jet r ω ∈ CrClosed r (m + 1) n),
      (faceCl r m n i ⟨jet r ω, hw⟩ : Jet r m × Jet r m) = jet r (pull m i ω)) := by sorry

end IntLInfty.Kan
