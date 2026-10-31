-- Prove2me | Theorems.Thm_InfoShareH2_lemma_2
-- name    : InfoShareH2.lemma_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:29:47.184981+00:00
-- url     : https://prove2.me/theorems/f70d6642-fea4-4cf7-92ea-995479da6ba6
-- title:
--   Lemma 2 — Smirnov–Beurling inner–outer factorization $\tilde\psi=Q\,B\,G$ (corrected: (32) in the orientation of (29))
-- statement:
--   Let $\tilde\psi\in H^2$ be nonzero, with boundary values $\tilde\psi(e^{i\lambda})$ on the unit circle. Then:
--
--   1. $\lambda\mapsto\log|\tilde\psi(e^{-i\lambda})|$ is integrable on $(-\pi,\pi]$;
--   2. the function
--   $$Q(z)=\exp\Bigl(\frac1{2\pi}\int_{-\pi}^{\pi}\frac{e^{i\lambda}+z}{e^{i\lambda}-z}\log|\tilde\psi(e^{i\lambda})|\,d\lambda\Bigr),\qquad |z|<1,$$
--   belongs to $H^2$ and is outer;
--   3. there is an inner function $M\in H^2$ with $\tilde\psi=QM$ on the disk, and it is the only inner function with this property;
--   4. $M=BG$ on the disk, where $B\in H^2_B$ is a Blaschke product whose zeros in the disk are those of $\tilde\psi$, with the same multiplicities, and $G\in H^2_S$ is a singular inner function with constant $1$.
--
--   This factorization reduces the no-sharing problem (26) to an optimization over the three factors: the outer factor alone determines $\sigma^2_{S|NS}$, and the inner factors only affect the inventory variance.
--
--   Differences from the source:
--   - correction: (32): log|ψ̃(e^{−iλ})| against the kernel (e^{iλ} + z)/(e^{iλ} − z) → log|ψ̃(e^{iλ})|, the orientation of (29); reason: for complex coefficients the printed (32) is not the outer factor: ψ̃(z) = 1 + iz/2 is nonzero and outer, the printed Q has |Q(e^{iπ/2})| = |ψ̃(e^{−iπ/2})| = 3/2 while |ψ̃(e^{iπ/2})| = 1/2, so ψ̃/Q is not inner; for real coefficients both agree
--   - reading: Blaschke product (30) B = z^{m₀}∏(z − z_k)/(1 − z̄_k z); G of (31) with a constant c ∈ T → B = c·z^{m₀}∏(|z_k|/z_k)(z_k − z)/(1 − z̄_k z) with |c| = 1; G with c = 1; reason: (30) diverges for zeros accumulating away from −1; the footnote on p.24 allows a unimodular constant; this convention reproduces (30) whenever it converges and is the one under which Lemmas 3, 6 and Proposition 6 hold
--   - reading: "B is a Blaschke product that includes the zeros of ψ̃ in D" → the order of vanishing of B equals that of ψ̃ at every point of D; reason: zeros counted with multiplicity (p.24)
--   - encoding: H², functions on T, "integrable on T", B ∈ H²_B, G ∈ H²_S → ℓ² coefficient sequences; radial limits; IntegrableOn over (−π, π]; representation data with square-summable Taylor coefficients; reason: Lean representation of the same objects
-- source:
--   Caldentey–Giloni–Hurvich–Zhang, Information Design and Sharing in Supply Chains, SSRN 4319721 (v. 2024-01-20), https://ssrn.com/abstract=4319721, Lemma 2, pp.24–25, (32) p.24 (cited: Rudin 1987, Thm 17.17)

import Mathlib
import Definitions.Def_InfoShareH2_Model
import Definitions.Def_InfoShareH2_Hardy

open Filter Topology MeasureTheory Complex

set_option autoImplicit false

namespace InfoShareH2

/-- **Lemma 2 (Smirnov–Beurling inner–outer factorization).**
SSRN 4319721 (v. 2024-01-20), Lemma 2, pp.24–25 (cited from Rudin 1987, Thm 17.17). "For any
nonzero function `ψ̃ ∈ H²`, `log |ψ̃|` is integrable on `T`, and `ψ̃` can be factorized uniquely as
`ψ̃(z) = Q(z)M(z)`, where `Q(z) ∈ H²_O` is the outer function (32) and `M(z)` is an inner function.
Furthermore, … `M(z) = B(z)G(z)`, where `B(z) ∈ H²_B` is a Blaschke product that includes the zeros
of `ψ̃` in `D` and `G(z) ∈ H²_S` is a singular inner function."

**Formalization Note** (corrected) `Q` is the Szegő function in the orientation of (29),
`log |ψ̃(e^{iλ})|` against the kernel `(e^{iλ} + z)/(e^{iλ} − z)`; the printed (32) has
`log |ψ̃(e^{−iλ})|`, which is not the outer factor for complex coefficients
(`ψ̃(z) = 1 + iz/2`). For real coefficients the two agree. "Includes the zeros of `ψ̃`" is equality
of the orders of vanishing at every point of `D`. The singular inner factor is normalized with
constant `1`; the unimodular constant is carried by `B` (footnote, p.24). `B ∈ H²_B` and `G ∈ H²_S`
include that their Taylor coefficients are square summable. Uniqueness is that of `M` given `Q`. -/
theorem lemma_2 (a : ℕ → ℂ) (ha : a ∈ H2) (hne : a ≠ 0) :
    IntegrableOn (fun lam => Real.log ‖boundary a lam‖) (Set.Ioc (-Real.pi) Real.pi) ∧
    (∃ q : ℕ → ℂ, IsOuter q ∧ ∀ z ∈ Disk, zTransform q z = outerPart a z) ∧
    ∃ m : ℕ → ℂ, IsInner m ∧ (∀ z ∈ Disk, zTransform a z = outerPart a z * zTransform m z) ∧
      (∀ m' : ℕ → ℂ, IsInner m' →
        (∀ z ∈ Disk, zTransform a z = outerPart a z * zTransform m' z) → m' = m) ∧
      ∃ (B : BlaschkeData) (G : SingularData), G.c = 1 ∧
        Memℓp (taylorCoeff B.eval) 2 ∧ Memℓp (taylorCoeff G.eval) 2 ∧
        (∀ z ∈ Disk, zTransform m z = B.eval z * G.eval z) ∧
        ∀ w ∈ Disk, analyticOrderAt B.eval w = analyticOrderAt (zTransform a) w := by sorry

end InfoShareH2
