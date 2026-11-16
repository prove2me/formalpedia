-- Prove2me | Theorems.Thm_NCFactorClosure607_Circuits_Supplement_vnp_factor_closure
-- name    : NCFactorClosure607.Circuits.Supplement.vnp_factor_closure
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:12:14.194293+00:00
-- url     : https://prove2.me/theorems/c9484b89-fe30-4721-bc0d-b31a426b7b29
-- title:
--   Theorem 6.1 — $\mathrm{VNP}_{nc}$ is closed under factors; verifiers of size $O(sd^3)$, $O(sd^6)$ and degree $\le d$
-- statement:
--   Let $F$ be any field, $X$ a set of noncommuting variables and $Z=\{z_1,\dots,z_t\}$ Boolean variables. Over every field $\mathrm{VNP}_{nc}$ is closed under taking factors. Quantitatively, there is an absolute constant $K$ such that: if $f\neq0$ has a representation
--   $$f(X)=\sum_{e\in\{0,1\}^t}G(X,e)$$
--   whose verifier $G\in F\langle X\cup Z\rangle$ has circuit size $s$ and degree at most $d$, where $d\ge1$, then
--
--   1. if $f=gh$, then $g=\sum_{e\in\{0,1\}^t}H(X,e)$ for a verifier $H$ of circuit size at most $Ksd^3$ and degree at most $d$, and the same bounds hold for the right factor $h$;
--   2. if $f=aqk$, then $q$ has a verifier of circuit size at most $Ksd^6$ and degree at most $d$.
--
--   The new verifiers use the same Boolean variables $Z$. The theorem does not assume a small circuit for $f$ itself; it supplies the $\mathrm{VNP}_{nc}$ clause of Theorem 1.2.
--
--   Differences from the source:
--   - generalization: X = {x_1, …, x_m} with m ≥ 1 → an arbitrary type X of noncommuting variables; reason: the statement for every type specializes to every finite nonempty variable set
--   - encoding: X ∪ Z with Z = {z_1, …, z_t}; G(X, e) replaces z_j by the scalar e_j → variables X ⊕ Fin t; the algebra map fixing X and sending z_j to 1 or 0 for e_j true or false; reason: the same objects
--   - encoding: O(sd³) and O(sd⁶) → one absolute natural constant K quantified before the field, the variable type, the input and the factors; reason: the O(·) of the source is a uniform absolute constant
--   - reading: A constant verifier is handled by scalar arithmetic → no separate clause; a constant verifier has degree ≤ d for d ≥ 1 and is covered by (i) and (ii); reason: the sentence describes the proof of a covered case
--   - encoding: Over every field, VNPnc is closed under taking factors → ClosedUnderFactors F (VNPnc F) for every field F; reason: the class and closure notion of §6.2 and Theorem 1.2
-- source:
--   V. Arvind, Pushkar S Joglekar, Factor Closure in Noncommutative Algebraic Complexity, STOC 2027 submission #607 (October 2026), p.15, Theorem 6.1, eq. (16); proof pp.15–16; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/607.pdf

import Mathlib
import Definitions.Def_NCFactorClosure607_Circuits_Supplement_Classes

universe u v

namespace NCFactorClosure607.Circuits.Supplement

open NCFactorClosure607.Circuits

/-- Theorem 6.1 (VNP factor closure), p.15. Over every field `VNP_nc` is closed under taking
factors. Quantitatively, there is one absolute constant `K` such that for every field `F`, every
type `X` of noncommuting variables, every number `t` of Boolean variables and every verifier
`G ∈ F⟨X ∪ Z⟩` computed by a circuit of size `s`, of degree at most `d ≥ 1`, representing
`f = Σ_{e ∈ {0,1}^t} G(X, e) ≠ 0` (eq. (16)):
(i) if `f = g h`, then `g = Σ_e H(X, e)` for a verifier `H` on the same Boolean variables of
circuit size at most `K s d³` and degree at most `d`, and the same holds for the right factor `h`;
(ii) if `f = a q k`, then `q` has such a verifier of circuit size at most `K s d⁶` and degree at
most `d`. -/
theorem vnp_factor_closure :
    (∀ (F : Type u) [Field F], ClosedUnderFactors F (VNPnc F)) ∧
    ∃ K : ℕ, ∀ (F : Type u) [Field F] (X : Type v) (t : ℕ) (G : Circuit F (X ⊕ Fin t)) (d : ℕ),
      G.WellFormed → 1 ≤ d → DegLE G.eval d → boolSum G.eval ≠ 0 →
      (∀ g h : FreeAlgebra F X, boolSum G.eval = g * h →
        (∃ H : Circuit F (X ⊕ Fin t), H.WellFormed ∧ H.size ≤ K * G.size * d ^ 3 ∧
          DegLE H.eval d ∧ boolSum H.eval = g) ∧
        (∃ H : Circuit F (X ⊕ Fin t), H.WellFormed ∧ H.size ≤ K * G.size * d ^ 3 ∧
          DegLE H.eval d ∧ boolSum H.eval = h)) ∧
      (∀ a q k : FreeAlgebra F X, boolSum G.eval = a * q * k →
        ∃ H : Circuit F (X ⊕ Fin t), H.WellFormed ∧ H.size ≤ K * G.size * d ^ 6 ∧
          DegLE H.eval d ∧ boolSum H.eval = q) := by sorry

end NCFactorClosure607.Circuits.Supplement
