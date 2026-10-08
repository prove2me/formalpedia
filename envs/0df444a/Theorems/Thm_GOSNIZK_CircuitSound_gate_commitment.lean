-- Prove2me | Theorems.Thm_GOSNIZK_CircuitSound_gate_commitment
-- name    : GOSNIZK.CircuitSound.gate_commitment
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T10:30:28.776011+00:00
-- url     : https://prove2.me/theorems/5d9fd80e-f25d-4e51-b730-ae354f099359
-- title:
--   The gate commitment c₀ · c₁ · c₂² · com(−2; 0) commits to b₀ + b₁ + 2b₂ − 2, and a 0/1 proof for it shows b₂ = ¬(b₀ ∧ b₁)
-- statement:
--   Let a homomorphic proof commitment scheme have message space $\mathcal M=\mathbb Z/N\mathbb Z$ with $N\ge4$, and assume the homomorphic property, perfect binding and perfect soundness of the 0/1 proof.
--
--   1. For every key $ck$ of either mode, all messages $m_0,m_1,m_2$ and randomizers $r_0,r_1,r_2$,
--   $$\mathrm{com}(m_0;r_0)\cdot\mathrm{com}(m_1;r_1)\cdot\mathrm{com}(m_2;r_2)^2\cdot\mathrm{com}(-2;0)=\mathrm{com}(m_0+m_1+2m_2-2;\ r_0+r_1+2r_2).$$
--   2. For every $(ck,xk)$ output by $K_{\mathrm{binding}}$, all bits $b_0,b_1,b_2$, randomizers $r_0,r_1,r_2$ and every $\pi$: if
--   $$V_{01}\big(ck,\ \mathrm{com}(b_0;r_0)\,\mathrm{com}(b_1;r_1)\,\mathrm{com}(b_2;r_2)^2\,\mathrm{com}(-2;0),\ \pi\big)=1,$$
--   then $b_2=\neg(b_0\wedge b_1)$.
--
--   This is the gate check of Figure 3: the verifier can test a NAND gate on committed wires with one 0/1 proof.
--
--   **Formalization Note** Part 2 is the paper's sentence "A proof that this commitment contains 0 or 1 shows that $b_2=\neg(b_0\wedge b_1)$", made precise: the proof is accepted on a binding key, and perfect binding identifies the message it certifies with $b_0+b_1+2b_2-2$, to which Lemma 5 applies.
-- source:
--   Groth, Ostrovsky, Sahai, New Techniques for Noninteractive Zero-Knowledge, J. ACM 59(3) (2012), authors' version of March 7, 2011, p. 14, paragraph after Lemma 5

import Mathlib
import Definitions.Def_GOSNIZK_CircuitSound_Protocol

namespace GOSNIZK.CircuitSound

/-- The gate commitment (Groth, Ostrovsky, Sahai, *New Techniques for Noninteractive
Zero-Knowledge*, J. ACM 59(3) (2012), authors' version of March 7, 2011, p. 14, after Lemma 5).
(1) Under the homomorphic property, on every key of either mode,
`com(b₀; r₀) · com(b₁; r₁) · com(b₂; r₂)² · com(−2; 0) = com(b₀ + b₁ + 2b₂ − 2; r₀ + r₁ + 2r₂)`.
(2) On a binding key, with message space of order at least 4, perfect binding and perfect soundness
of the 0/1 proof, an accepted 0/1 proof for this commitment, where `b₀, b₁, b₂` are bits, shows
`b₂ = ¬(b₀ ∧ b₁)`. -/
theorem gate_commitment {N : ℕ} {R C CK XK TK Rp Prf : Type} [AddCommGroup R] [Fintype R] [CommGroup C] [Fintype C]
    [Fintype Rp] [Nonempty Rp] (S : Scheme N R C CK XK TK Rp Prf)
    (hN : 4 ≤ N) (hhom : S.Homomorphic) (hbind : S.PerfectBinding)
    (hsound01 : S.PerfectSoundness01) :
    (∀ ck : CK, S.IsKey ck → ∀ (m₀ m₁ m₂ : ZMod N) (r₀ r₁ r₂ : R),
      S.gateCom ck (S.com ck m₀ r₀) (S.com ck m₁ r₁) (S.com ck m₂ r₂) =
        S.com ck (m₀ + m₁ + 2 * m₂ - 2) (r₀ + r₁ + 2 • r₂)) ∧
    (∀ (ck : CK) (xk : XK), (ck, xk) ∈ S.Kbind.support →
      ∀ (b₀ b₁ b₂ : Bool) (r₀ r₁ r₂ : R) (π : Prf),
        S.V01 ck (S.gateCom ck (S.com ck (ofBit b₀) r₀) (S.com ck (ofBit b₁) r₁)
          (S.com ck (ofBit b₂) r₂)) π = true →
        b₂ = !(b₀ && b₁)) := by sorry

end GOSNIZK.CircuitSound
