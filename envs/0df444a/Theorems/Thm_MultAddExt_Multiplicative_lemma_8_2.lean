-- Prove2me | Theorems.Thm_MultAddExt_Multiplicative_lemma_8_2
-- name    : MultAddExt.Multiplicative.lemma_8_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T01:48:37.658755+00:00
-- url     : https://prove2.me/theorems/d6b6c273-1e2d-4182-af18-fb5b2604d808
-- title:
--   Lemma 8.2 — reconstruction: a complete and sound line test yields a small single-valued nondeterministic circuit for f̂
-- statement:
--   Let $q=2^\kappa$, $d\ge 1$ and $\hat h\ge 0$ be integers, $\mathbb F_q$ written in binary through an $\mathbb F_2$-basis, and $\hat f:\mathbb F_q^d\to\mathbb F_q$ a polynomial of total degree at most $\hat h$. Let $\mathrm{Thr}(w,a)$ be a nondeterministic circuit of size $S$ with inputs $w\in\mathbb F_q^d$, $a\in\mathbb F_q$. For a nondegenerate line $L$ and $p\in\mathbb F_q[t]$ of degree at most $\hat h$, $\mathrm{Test}_L(p)=\Pr_{t\leftarrow\mathbb F_q}[\mathrm{Thr}(L(t),p(t))=1]$; $\mathrm{Test}_L=0$ for degenerate $L$; and $P_L=\{p\in\mathbb F_q[t]:\deg p\le\hat h,\ \mathrm{Test}_L(p)>3/4\}$. Suppose
--   $$\Pr_{L\leftarrow\mathrm{RandLine}}\Bigl[\mathrm{Test}_L(\hat f\circ L)\ge\tfrac78,\ \ |P_L|\le\frac{q}{32(\hat h+1)}\Bigr]\ge\frac{31}{32}.$$
--   Then there is a single-valued nondeterministic circuit $C$ of size $\mathrm{poly}(S,\hat h,d,\log q)$ with $\mathrm{ACCEPT}_C(x)=\{\hat f(x)\}$ for every $x\in\mathbb F_q^d$.
--
--   It turns a test that is complete and sound for the low-degree extension of the hard function into a small circuit computing it, which contradicts $H_{NP}$ in §§9–10.
--
--   Differences from the source:
--   - encoding: Boolean circuits over an unspecified basis; size includes input, output and witness lengths (p. 18) → Circ: fan-in-two AND/OR and NOT gates (published QCSepTotal.Gates), with fixed Boolean constant wires; size = gates + variable inputs + outputs; NondetCirc / MultiNondetCirc use a Circ on (x, wit), counting witness bits in size; reason: a standard complete basis, including constants at zero input length; the paper fixes no basis, and changing the treatment of constant wires costs at most two gates
--   - encoding: F_q with q a power of two; circuits read and write field elements → any finite field F with an F₂-algebra structure and a basis B : Fin κ → F over ZMod 2 (q = 2^κ); elements written by their B-coordinates; the statement holds for every such B; reason: every field of order 2^κ is of this form; the paper fixes no binary encoding, and quantifying over every F₂-basis covers each natural one
--   - reading: size poly(S, ĥ, d, log q) → ∃ c₀ a₀ ∈ ℕ fixed before all other quantifiers, size ≤ c₀·(sum of the parameters + 1)^{a₀}; reason: the paper's polynomial bound is one absolute polynomial (the proofs of §9–§10 use absolute constants C₀, a₀); a polynomial in nonnegative quantities is bounded by such an expression and conversely
--   - encoding: Test_L(f̂ ∘ L) for the univariate polynomial f̂ ∘ L; |P_L| → lineTest applied to t ↦ f̂(L(t)); Set.ncard of P_L; reason: Test_L only evaluates its argument at points t; P_L is finite (polynomials of degree ≤ ĥ over a finite field), natDegree ≤ ĥ includes 0
-- source:
--   Ball, Chattopadhyay, Gurumukhani, Shaltiel, Zhao, Multiplicative and Additive Extractors for Low Entropy Samplable Sources Under Reduced Assumptions, STOC 2027 submission (manuscript sha256 5ac077d7…), p. 46 (PDF 50), Lemma 8.2

import Mathlib
import Definitions.Def_MultAddExt_Multiplicative_FinDist
import Definitions.Def_MultAddExt_Multiplicative_NondetCircuit
import Definitions.Def_MultAddExt_Multiplicative_FieldCircuits

set_option autoImplicit false

namespace MultAddExt.Multiplicative

/-- **Lemma 8.2** (Reconstruction from a polynomial test), p. 46. Let `q = 2^κ`, `d ≥ 1`, `ĥ ≥ 0`,
`f̂ : F_q^d → F_q` a polynomial of total degree at most `ĥ`, and `Thr(w, a)` a nondeterministic
circuit of size `S`. With `Test_L` the line test (`0` on degenerate lines) and
`P_L = {p ∈ F_q[t] : deg p ≤ ĥ, Test_L(p) > 3/4}`, suppose
`Pr_{L ← RandLine}[Test_L(f̂ ∘ L) ≥ 7/8, |P_L| ≤ q/(32(ĥ + 1))] ≥ 31/32`. Then there is a
single-valued nondeterministic circuit `C` of size `poly(S, ĥ, d, log q)` with
`ACCEPT_C(x) = {f̂(x)}` for every `x ∈ F_q^d`. -/
theorem lemma_8_2 : ∃ c₀ a₀ : ℕ, ∀ {F : Type} [Fintype F] [Field F] [Algebra (ZMod 2) F]
    {κ : ℕ} (B : Module.Basis (Fin κ) (ZMod 2) F) (d h : ℕ), 1 ≤ d →
    ∀ fhat : MvPolynomial (Fin d) F, fhat.totalDegree ≤ h →
    ∀ Thr : NondetCirc (d * κ + κ),
      (31 / 32 : ℝ) ≤ randLineProb (fun u v =>
        (7 / 8 : ℝ) ≤ lineTest B Thr u v (fun t => MvPolynomial.eval (line u v t) fhat) ∧
        ({p : Polynomial F | p.natDegree ≤ h ∧ 3 / 4 < lineTest B Thr u v (fun t => p.eval t)}.ncard
          : ℝ) ≤ (Fintype.card F : ℝ) / (32 * ((h : ℝ) + 1))) →
      ∃ C : MultiNondetCirc (d * κ) κ,
        (C.size : ℝ) ≤ c₀ * ((Thr.size + h + d + κ : ℝ) + 1) ^ a₀ ∧
        ∀ x, acceptF B C x = {MvPolynomial.eval x fhat} := by sorry

end MultAddExt.Multiplicative
