-- Prove2me | Theorems.Thm_IntegerMatrixMortality_FixedImage_state_and_digit_checks
-- name    : IntegerMatrixMortality.FixedImage.state_and_digit_checks
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T14:34:22.074077+00:00
-- url     : https://prove2.me/theorems/2c63b801-5c74-48af-b418-bc426cbbd072
-- title:
--   Lemma 5.4 — State and digit checks
-- statement:
--   Let the phases be indexed below N and let p≥7 be prime with p>6N. Take any generator A=Cᵣ Mδ,k Dₑ M₁,h Cq⁻¹ with q,r<N, e∈Δ={−1,0,1,2,3,4}. It preserves E. If its input is Cq₀(z), with q₀<N, z∈V and residue d∈Δ, then
--
--   $$A(C_{q_0}(z))\in V\implies q=q_0\ \text{and}\ e=d.$$
--
--   The whole bracket is one matrix. This statement checks both the phase and digit, even for a wrongly guessed arithmetic value.
--
--   Differences from the source:
--   - encoding: rational projective points, residues and matrix words → Option ℚ with explicit poles, reduced-denominator congruence and reversed list products; reason: infinity and empty words have their source values
-- source:
--   Thanin Quartz, Ivan O. Shevchenko, Hans De Sterck, Jun Liu, STOC 2027 submission #1062 (October 2026), Lemma 5.4, PDF p. 10 / printed p. 8

import Definitions.Def_IntegerMatrixMortality_FixedImage_ScanInterfaces

set_option autoImplicit false

namespace IntegerMatrixMortality.FixedImage

theorem state_and_digit_checks
    (p N : ℕ) (hp : Nat.Prime p) (hp7 : 7 ≤ p) (hN : 6*N < p)
    (e : GeneratorEdge) (hs : e.source < N) (ht : e.target < N) (he : e.digit ∈ delta) :
      (∀ x, Error p x → Error p (projectiveAction (rationalMatrix (edgeMatrix p e)) x)) ∧
      ∀ q₀ z d, q₀ < N → d ∈ delta → HasResidue p z d →
        Valid p (projectiveAction (rationalMatrix (edgeMatrix p e)) (shift q₀ z)) →
          e.source = q₀ ∧ e.digit = d := by sorry

end IntegerMatrixMortality.FixedImage
