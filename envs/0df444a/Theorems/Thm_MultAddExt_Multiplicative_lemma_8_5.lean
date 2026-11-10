-- Prove2me | Theorems.Thm_MultAddExt_Multiplicative_lemma_8_5
-- name    : MultAddExt.Multiplicative.lemma_8_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T01:48:47.657976+00:00
-- url     : https://prove2.me/theorems/29a927e4-2b3f-4409-9fd6-e3e6d0297f39
-- title:
--   Lemma 8.5 — nondeterministic local correction of a low-degree polynomial from 15/16 agreement
-- statement:
--   Let $\mathbb F_q$ be a field with $q=p^\kappa$ elements for an arbitrary prime $p$, written in binary through an $\mathbb F_p$-basis, and let $g:\mathbb F_q^d\to\mathbb F_q$ be a polynomial of total degree at most $\hat h$, where $q-1\ge 4(\hat h+1)$. Suppose a (multi-output) nondeterministic circuit $C$ of size $S$ satisfies
--   $$\Pr_{x\leftarrow\mathbb F_q^d}\bigl[\mathrm{ACCEPT}_C(x)=\{g(x)\}\bigr]\ge\frac{15}{16}.$$
--   Then there is a single-valued nondeterministic circuit $C^*$ with $\mathrm{ACCEPT}_{C^*}(x)=\{g(x)\}$ for every $x\in\mathbb F_q^d$, of size polynomial in $S,\hat h,d,\log q$ with an absolute polynomial bound: $\mathrm{size}(C^*)\le c_0(S+\hat h+d+L+1)^{a_0}$ for absolute $c_0,a_0$.
--
--   It is the last step of the reconstruction argument (Lemma 8.2).
--
--   Here L = κ·Nat.size p is the encoding length, between log₂ q and twice log₂ q. The accepted-bit set must equal the singleton encoding of g(x); invalid accepted words are not silently discarded.
--
--   Differences from the source:
--   - encoding: Boolean circuits over an unspecified basis; size includes input, output and witness lengths (p. 18) → Circ: fan-in-two AND/OR and NOT gates (published QCSepTotal.Gates), with fixed Boolean constant wires; size = gates + variable inputs + outputs; NondetCirc / MultiNondetCirc use a Circ on (x, wit), counting witness bits in size; reason: a standard complete basis, including constants at zero input length; the paper fixes no basis, and changing the treatment of constant wires costs at most two gates
--   - encoding: an arbitrary finite field F_q and circuits reading and writing field elements → a basis B of F over ZMod p for an arbitrary prime p; binary canonical residues of the κ coefficients, of total length L = κ·Nat.size p; exact singleton equality of accepted bit strings; reason: every finite field admits this representation; log₂ q ≤ L ≤ 2 log₂ q and field arithmetic has polynomial-size circuits in L for every basis; this preserves the absolute polynomial bound and includes odd characteristic
--   - reading: size polynomial in S, ĥ, d, log q, with an absolute polynomial bound → ∃ c₀ a₀ ∈ ℕ fixed before all other quantifiers, size ≤ c₀·(sum of the parameters + 1)^{a₀}; reason: the paper's polynomial bound is one absolute polynomial (the proofs of §9–§10 use absolute constants C₀, a₀); a polynomial in nonnegative quantities is bounded by such an expression and conversely
-- source:
--   Ball, Chattopadhyay, Gurumukhani, Shaltiel, Zhao, Multiplicative and Additive Extractors for Low Entropy Samplable Sources Under Reduced Assumptions, STOC 2027 submission (manuscript sha256 5ac077d7…), p. 48 (PDF 52), Lemma 8.5

import Mathlib
import Definitions.Def_MultAddExt_Multiplicative_FinDist
import Definitions.Def_MultAddExt_Multiplicative_NondetCircuit
import Definitions.Def_MultAddExt_Multiplicative_FieldCircuits

set_option autoImplicit false

namespace MultAddExt.Multiplicative

/-- **Lemma 8.5** (Nondeterministic local correction), p. 48. Let `g : F_q^d → F_q` be a
polynomial of total degree at most `ĥ` with `q − 1 ≥ 4(ĥ + 1)`. If a nondeterministic circuit `C`
of size `S` satisfies `Pr_{x ← F_q^d}[ACCEPT_C(x) = {g(x)}] ≥ 15/16`, there is a single-valued
nondeterministic circuit `C*` with `ACCEPT_{C*}(x) = {g(x)}` for every `x`, of size polynomial in
`S, ĥ, d, log q` with an absolute polynomial bound. `F_q` has arbitrary prime characteristic `p` and is written in
binary through an `F_p`-basis `B`, using `p.size` bits per coefficient. -/
theorem lemma_8_5 : ∃ c₀ a₀ : ℕ, ∀ {p : ℕ} [Fact p.Prime] {F : Type} [Fintype F] [Field F] [Algebra (ZMod p) F]
    {κ d : ℕ} (B : Module.Basis (Fin κ) (ZMod p) F) (h : ℕ) (g : MvPolynomial (Fin d) F),
    g.totalDegree ≤ h → 4 * (h + 1) ≤ Fintype.card F - 1 →
    ∀ C : MultiNondetCirc (d * (κ * p.size)) (κ * p.size),
      (15 / 16 : ℝ) ≤ probEvent (uniform (Fin d → F)) {x | C.acceptSet (primeVecBits B x) = {primeFieldBits B (MvPolynomial.eval x g)}} →
      ∃ Cstar : MultiNondetCirc (d * (κ * p.size)) (κ * p.size),
        (Cstar.size : ℝ) ≤ c₀ * ((C.size + h + d + κ * p.size : ℝ) + 1) ^ a₀ ∧
        ∀ x, Cstar.acceptSet (primeVecBits B x) = {primeFieldBits B (MvPolynomial.eval x g)} := by sorry

end MultAddExt.Multiplicative
