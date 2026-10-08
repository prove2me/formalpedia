-- Prove2me | Theorems.Thm_GOSNIZK_CircuitZK_gate_opening
-- name    : GOSNIZK.CircuitZK.gate_opening
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T11:24:30.426178+00:00
-- url     : https://prove2.me/theorems/602c2817-055a-4e69-b1a7-6ae0d6fcd2f5
-- title:
--   Proof of Lemma 8, p. 15 — the simulated gate commitment $c_ic_jc_k^2\,\mathrm{com}(-2;0)$ opens to $0$ with $r_i+r_j+2r'_k$
-- statement:
--   Let the commitment scheme be homomorphic with perfect trapdoor opening, and let $(ck, tk)$ be a hiding key. Consider a NAND gate with wires $i, j, k$ whose commitments are $c_i = \mathrm{com}(0; r_i)$, $c_j = \mathrm{com}(0; r_j)$ and $c_k = \mathrm{com}(0; r_k)$, and let $r'_k = \mathrm{Topen}_{tk}(0, r_k, 1)$ be the trapdoor opening of $c_k$ to $1$. Then
--   $$c_i\, c_j\, c_k^2\, \mathrm{com}(-2; 0) = \mathrm{com}\big(0;\ r_i + r_j + 2r'_k\big).$$
--
--   So the simulator, which committed to $0$ on every wire, knows an opening of each gate commitment to the message $0$ and can make the gate's 0/1 proof with it.
--
--   **Formalization Note** The page writes the randomizer as $r_i + r_j + 2r'_j$; the opening of $c_k$ to $1$ is $r'_k$, and the statement uses $r'_k$.
-- source:
--   Groth, Ostrovsky, Sahai, New Techniques for Noninteractive Zero-Knowledge, J. ACM 59(3) (2012), authors' version of March 7, 2011, p. 15, proof of Lemma 8 (the gate witness (0, r_i + r_j + 2r'_k); the page prints 2r'_j)

import Mathlib
import Definitions.Def_GOSNIZK_CircuitZK_Scheme

namespace GOSNIZK.CircuitZK

/-- Proof of Lemma 8 (Groth, Ostrovsky, Sahai, J. ACM 59(3) (2012), authors' version of March 7, 2011, p. 15),
the simulated gate opening. On a hiding key `(ck, tk)`, let a NAND gate have wires `i, j, k` whose commitments are
`c_i = com(0; r_i)`, `c_j = com(0; r_j)`, `c_k = com(0; r_k)`, and let `r'_k = Topen_tk(0, r_k, 1)` (so that
`c_k = com(1; r'_k)`). Then `c_i c_j c_k² com(−2; 0) = com(0; r_i + r_j + 2r'_k)`, i.e. `(0, r_i + r_j + 2r'_k)` is an
opening of the gate commitment to `0`. The page writes `2r′_j`; the opening of `c_k` is `r′_k`. -/
theorem gate_opening {N : ℕ} {R C CK XK TK Rp Pf : Type} [AddCommGroup R] [CommGroup C]
    (S : Scheme N R C CK XK TK Rp Pf) (hhom : S.Homomorphic) (hTO : S.PerfectTrapdoorOpening)
    (kt : CK × TK) (hkt : kt ∈ S.Khide.support) (rᵢ rⱼ rₖ : R) :
    S.com kt.1 0 rᵢ * S.com kt.1 0 rⱼ * S.com kt.1 0 rₖ ^ 2 * S.com kt.1 (-2) 0 =
      S.com kt.1 0 (rᵢ + rⱼ + 2 • S.Topen kt.2 0 rₖ 1) := by sorry

end GOSNIZK.CircuitZK
