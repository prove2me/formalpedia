-- Prove2me | Theorems.Thm_HardyFLocal_clumped_causaloid_specifies_qubits
-- name    : HardyFLocal.clumped_causaloid_specifies_qubits
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:41:20.004688+00:00
-- url     : https://prove2.me/theorems/eab8a5d0-998d-402e-a6da-4583fffbdf35
-- title:
--   §5, (27)–(28), p.14 (corrected: fiducial clause and "only if" for interior regions) — the clumped causaloid fully specifies the qubit theory
-- statement:
--   Let $m,n$ be natural numbers, $\rho$ a density matrix on the $m+n$ qubits of the lattice, and $M$ the experiment model of the lattice. Let $\$_k$ be a fiducial family with $\$_1=I$, $L$ fiducial labels, and $C$ the causaloid of the lattice, built from the elementary table, the pair table and the clumping method. Then:
--
--   1. **(Every probability, every region.)** For every finite set $O$ of vertices, every label $\alpha$ of $R_O$ and every generalized preparation $s$,
--   $$p_\alpha=\mathbf r_\alpha(R_O)\cdot\mathbf p(R_O).$$
--   2. **(Minimality, interior regions.)** If $O$ has no vertex at either end of a qubit, the clump labels $\Omega_C(O)$ are a fiducial set of $R_O$.
--   3. **(The two-step approach.)** Let $O_1,O_2$ be disjoint, $\alpha_1$ a label of $R_1$, and $F_2$ a setting with outcomes $Y_2$ on $O_2$. Put
--   $$a=\mathbf r_{\alpha_1\alpha_2},\qquad b=\sum_{\beta_2}\mathbf r_{\alpha_1\beta_2},$$
--   both computed from $C$, where $\beta_2$ runs over the outcome families of $F_2$. Then
--      - (a) both sums over $\beta_2$, of the vectors and of the probabilities under each $s$, are summable;
--      - (b) the joint probability is $a\cdot\mathbf p(R_1\cup R_2)$ and the probability of the conditioning event is $b\cdot\mathbf p(R_1\cup R_2)$, for every $s$;
--      - (c) if $a=c\,b$, then $c$ is the value of $\mathrm{Prob}(Y_2\mid Y_1,F_1,F_2)$, and if moreover $b\ne0$, so is $|a|/|b|$ (19), whatever the region;
--      - (d) if $O_1\cup O_2$ has no vertex at either end of a qubit: the probability is well defined if and only if $a=c\,b$ for some $c$; every value $c$ satisfies $a=c\,b$; if $b\ne0$, every value equals $|a|/|b|$; and $b=0$ if and only if the conditioning event has probability $0$ under every preparation.
--   4. **(F-locality.)** For tables $(T,E)$, $(T',E')$ that agree on the sequential pairs of vertices inside $O$ and on the vertices of $O$, the two clumped causaloids have the same $\Omega_C(O)$, the same $\Lambda(O)$, and the same $\mathbf r_\alpha(R_O)$ for every $\alpha$.
--
--   This is the paper's closing claim for quantum theory: the causaloid separates the specification of the theory from the way it is used to make predictions, and everything about a region is computed from objects of that region.
--
--   **Formalization Note** The statement holds for every lattice size, every density matrix, every fiducial family and all fiducial labels. Well-definedness is the ratio statement of the published `HardyCausaloid.CondWellDefined`. The fiducial clause cannot use `HardyCausaloid.IsCausaloidOf`, which asks for it at every region.
--
--   Differences from the source:
--   - correction: the clumping method and the two-step test apply to "an arbitrary region" and "an arbitrary probability" (p.14), with fiducial sets minimal (p.9) and (18) an if and only if (p.11) → minimality and the "only if" of (18) are stated for Interior regions, with no vertex at either end of a qubit; computing probabilities and the "if" direction stay at every region; reason: false as printed: on a 1 x 1 lattice with O1 empty, O2 the whole lattice and a sigma_z measurement of the right mover, every assumption of the source holds and the probability is well defined (one preparation), yet a is not a multiple of b; proved in the verification file
--   - reading: "a large number" of qubits → every m, n in ℕ, including small ones; reason: the statement is uniform in the lattice size and states nothing different on small lattices
--   - encoding: the labelling sentence of p.12 has v running from right to left → on a right mover (u, v) is followed by (u, v+1), on a left mover (u, v) by (u+1, v); reason: the explicit statement of p.13; it differs only by reversing both labellings
--   - reading: superoperators are "trace non-increasing maps on density operators that take allowed states to allowed states" → completely positive (finite Kraus form) and trace non-increasing; reason: the standard meaning; positivity alone fails on entangled inputs, which this lattice produces
--   - reading: "a general measurement" with a display panel, with no outcome count → an instrument with branches indexed by ℕ, zero branches allowed, HasSum normalization; reason: covers every finite instrument; the stronger reading, which adds the summability clause
--   - reading: the paper names no initial state → every density matrix on all the qubits, fixed once for the model; reason: entangled or not; the claim is uniform in it
--   - reading: a "fiducial spanning set of superoperators", with Λ in "a real vector space" (p.9) → a basis over ℝ of the Hermiticity-preserving one-qubit maps; reason: real coefficients are what p.9 requires, and they exist for Hermiticity-preserving maps
--   - reading: (21)–(22) take k′, k″ in {1} and k in Ω² → the earliest vertex of a clump carries the free label, later vertices the label 1, on each of the two qubits of a vertex; reason: this is the index placement of (21)–(22) applied to every clump
--   - encoding: the fiducial set has the smallest |Ω₁| (p.9) → the published HardyCausaloid.Fiducial, sufficient and inclusion-minimal; reason: for a linear span both mean a basis of the span of the rows of the table
--   - reading: "we only use Λ matrices pertaining to regions R̃₁ ⊆ R₁" → for tables T, E as arguments: tables agreeing on the sequential pairs inside O and the vertices of O give the same ΩC O, Λ O and r_α; reason: the informal remark, as a statement about which entries of the tables are read
--   - encoding: labels run from 1, and the first element of Ω² is 1 → labels are 0-based, and the first element of Ω² = Fin 16 is 0; reason: Lean convention; same instances
--   - encoding: no order of evaluation is named across incomparable vertices → boxes are applied in lexicographic order; reason: lexicographic order extends the order along every qubit, and boxes sharing no qubit commute (proved in the verification file), so any other extension gives the same number
--   - encoding: a generalized preparation is a choice in V − R₁ → a total label s, whose values on O are ignored through glue; reason: the convention of the published HardyCausaloid.Region; same preparations
--   - encoding: the probability is the trace of the state after all the boxes → the real part of that trace (latticeProb); reason: the trace is real on the positive semidefinite matrices the boxes produce; same values
--   - encoding: (19): if the vectors are parallel, the probability is |a|/|b| → the ratio |a|/|b| is asserted only when b ≠ 0; reason: at b = 0 the ratio is undefined (Lean has x / 0 = 0); this excludes only the undefined case
-- source:
--   L. Hardy, Formalism Locality in Quantum Theory and Quantum Gravity, arXiv:0804.0054v1, §5, eqs. (27)–(28), the clumping method and the closing claim, p.14; §4.4, eqs. (18)–(19), p.11

import Mathlib
import Definitions.Def_HardyCausaloid_Model
import Definitions.Def_HardyCausaloid_Region
import Definitions.Def_HardyCausaloid_Fiducial
import Definitions.Def_HardyCausaloid_Causaloid
import Definitions.Def_HardyCausaloid_Conditional
import Definitions.Def_HardyFLocal_Superoperator
import Definitions.Def_HardyFLocal_Instrument
import Definitions.Def_HardyFLocal_Lattice
import Definitions.Def_HardyFLocal_FiducialFamily
import Definitions.Def_HardyFLocal_ClumpCausaloid

set_option autoImplicit false

namespace HardyFLocal

open HardyCausaloid

/-- **The clumped causaloid fully specifies the quantum theory of pairwise interacting qubits
(corrected: the fiducial clause and the "only if" of the two-step test are for regions away from the
ends of the qubits)**, Hardy, *Formalism Locality in Quantum Theory and Quantum Gravity*,
arXiv:0804.0054v1, §5, eqs. (27)–(28), the clumping method and the closing claim, p.14 ("Given this
causaloid we can employ the standard techniques of the causaloid framework (the causaloid product and
the two step approach) to calculate whether an arbitrary probability is well defined and, if so, what
it is equal to. In this sense we can say that this causaloid fully specifies the quantum theory of
interacting qubits"), with the two-step approach, §4.4, eqs. (18)–(19), p.11.

For all `m`, `n`, every density matrix `ρ` on the qubits, the model `M` of the lattice, every fiducial
family `S` and all fiducial labels `L`, with `C` the causaloid of the lattice:

1. (every region) `p_α = r_α(R_O) · p(R_O)` for every `O`, `α`, `s`;
2. (interior regions) the clump labels are a fiducial set of `R_O`;
3. (two-step approach) for all disjoint `O₁`, `O₂`, every label `α₁` of `R₁`, and every setting `F₂`
   with outcome family `Y₂` on `O₂`, with `a = r_{α₁α₂}` and `b = Σ_{β₂} r_{α₁β₂}` computed from `C`:
   (a) both sums over `β₂` are summable;
   (b) the joint probability is `a · p` and the probability of the conditioning event is `b · p`;
   (c) if `a = c b`, then `c` is the value of `Prob(Y₂ | Y₁, F₁, F₂)`, and if moreover `b ≠ 0`, so is
   `|a| / |b|` ((19)) (every region);
   (d) for `O₁ ∪ O₂` interior: the probability is well defined iff `a = c b` for some `c`; every value
   `c` satisfies `a = c b`; if `b ≠ 0`, every value is `|a| / |b|`; and `b = 0` iff the conditioning
   event has probability `0` under every preparation;
4. (F-locality) for tables `(T, E)`, `(T', E')` that agree on the sequential pairs inside `O` and on
   the vertices of `O`, the two clumped causaloids have the same `ΩC O`, `Λ O` and `r_α(R_O)`.

**Formalization Note** Clauses 2 and 3(d) fail for an arbitrary region: take `O₁ = ∅`, `O₂` the whole
lattice and a `σ_z` measurement of one qubit, so that the probability is well defined while the
vectors are not parallel (proved in the mission's verification file, on a `1 × 1` lattice). -/
theorem clumped_causaloid_specifies_qubits {m n : ℕ} (ρ : GlobalMat m n) (hρ : IsDensity ρ)
    (M : Model (Setting m n) (Outcome m n)) (hM : IsLatticeModel ρ M) (S : FiducialFamily)
    (L : ∀ x : X m n, Ω × Ω → Label (Setting m n) (Outcome m n) x) (hL : IsFiducialLabels S L) :
    let C := actualCausaloid S L
    (∀ (O : Finset (X m n)) (α : Lab (Setting m n) (Outcome m n) O)
        (s : ∀ x, Label (Setting m n) (Outcome m n) x),
      regionTable M O α s = C.r O α ⬝ᵥ C.state M O s) ∧
    (∀ O : Finset (X m n), Interior O → Fiducial (regionTable M O) (C.fidSet O)) ∧
    (∀ O₁ O₂ : Finset (X m n), Disjoint O₁ O₂ →
      ∀ (α₁ : Lab (Setting m n) (Outcome m n) O₁) (F₂ : ∀ x : O₂, Setting m n x.1)
        (Y₂ : ∀ x : O₂, Outcome m n x.1 (F₂ x)),
        Summable (fun β₂ : (∀ x : O₂, Outcome m n x.1 (F₂ x)) =>
          C.r (O₁ ∪ O₂) (joinLab α₁ (labOf F₂ β₂))) ∧
        (∀ s, Summable (fun β₂ : (∀ x : O₂, Outcome m n x.1 (F₂ x)) =>
          regionTable M (O₁ ∪ O₂) (joinLab α₁ (labOf F₂ β₂)) s)) ∧
        (∀ s, condNum M α₁ F₂ Y₂ s = condA C α₁ F₂ Y₂ ⬝ᵥ C.state M (O₁ ∪ O₂) s ∧
          condDen M α₁ F₂ s = condB C α₁ F₂ ⬝ᵥ C.state M (O₁ ∪ O₂) s) ∧
        (∀ c : ℝ, condA C α₁ F₂ Y₂ = c • condB C α₁ F₂ → IsCondValue M α₁ F₂ Y₂ c ∧
          (condB C α₁ F₂ ≠ 0 → IsCondValue M α₁ F₂ Y₂
            (euclidLength (condA C α₁ F₂ Y₂) / euclidLength (condB C α₁ F₂)))) ∧
        (Interior (O₁ ∪ O₂) →
          (CondWellDefined M α₁ F₂ Y₂ ↔ ∃ c : ℝ, condA C α₁ F₂ Y₂ = c • condB C α₁ F₂) ∧
          (∀ c : ℝ, IsCondValue M α₁ F₂ Y₂ c → condA C α₁ F₂ Y₂ = c • condB C α₁ F₂) ∧
          (condB C α₁ F₂ ≠ 0 → ∀ c : ℝ, IsCondValue M α₁ F₂ Y₂ c →
            c = euclidLength (condA C α₁ F₂ Y₂) / euclidLength (condB C α₁ F₂)) ∧
          (condB C α₁ F₂ = 0 ↔ ∀ s, condDen M α₁ F₂ s = 0))) ∧
    ∀ (O : Finset (X m n)) (T T' : X m n → X m n → PairTable)
      (E E' : ∀ x : X m n, Label (Setting m n) (Outcome m n) x → Ω × Ω → ℝ),
      (∀ x ∈ O, ∀ x' ∈ O, IsSequentialPair x x' → T x x' = T' x x') →
      (∀ x ∈ O, E x = E' x) →
      (clumpCausaloid L T E).ΩC O = (clumpCausaloid L T' E').ΩC O ∧
      (∀ (l : ∀ x : O, omegaOne L x.1) (k : omegaC L O),
        (clumpCausaloid L T E).Λ O l k = (clumpCausaloid L T' E').Λ O l k) ∧
      ∀ α : Lab (Setting m n) (Outcome m n) O,
        (clumpCausaloid L T E).r O α = (clumpCausaloid L T' E').r O α := by sorry

end HardyFLocal
