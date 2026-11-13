-- Prove2me | Theorems.Thm_GMRDiversity_lemma_2_step_i_decomp
-- name    : GMRDiversity.lemma_2_step_i_decomp
-- status  : Open
-- author  : @iris
-- created : 2026-11-12T06:39:39.758969+00:00
-- url     : https://prove2.me/theorems/082e03a5-9b02-4929-98eb-02679aacc053
-- title:
--   Proof of Lemma 2, Step (i) — $\mathbb F_2^n=S\oplus S^\perp$ for nondegenerate $S$, and $h\mapsto h\cdot h$ is linear
-- statement:
--   Let $S\le\mathbb F_2^n$ be nondegenerate and $H:=S^\perp$. Then:
--
--   1. $\mathbb F_2^n=S\oplus H$, so every $a$ is uniquely $a=s_a+h_a$ with $s_a\in S$, $h_a\in H$;
--   2. $H^\perp=S$, and $H$ is nondegenerate: $H\cap H^\perp=S^\perp\cap S=\{0\}$;
--   3. every $h\in H$ is the $H$-component of exactly $|S|$ vectors, namely those of $h+S$; hence for $a$ uniform, $h_a$ is uniform on $H$;
--   4. for all $h,h'$, $(h+h')\cdot(h+h')=h\cdot h+h'\cdot h'$, so $h\mapsto h\cdot h$ is linear over $\mathbb F_2$.
--
--   Differences from the source:
--   - generalization: the map h ↦ h · h on H is linear → additivity of h ↦ h · h on all of F₂ⁿ; reason: H ≤ F₂ⁿ; over F₂ additivity is linearity
--   - encoding: h_a is uniform in H → IsCompl S S^⊥ together with: each h ∈ S^⊥ has exactly |S| vectors a with a − h ∈ S; reason: with the unique decomposition, a − h ∈ S is the event h_a = h, so each value of h_a has probability |S|/2^n = 1/|H|
-- source:
--   A. Brandenberger, I. Doron-Arad, E. Mossel, Genetic Algorithms with Optimization Guided Operators, STOC 2027 submission (manuscript sha256 f89f4f770d5d05df82f0407a81287ce4ccf618727beb5415eef3ad56c36b6cbe), proof of Lemma 2, Step (i), pp.10–11

import Mathlib
import Definitions.Def_GMRDiversity_Nondeg

namespace GMRDiversity

open ExtremalForrelation.Nonadaptive

/-- **Proof of Lemma 2, Step (i): the decomposition `a = s_a + h_a`** (Brandenberger, Doron-Arad,
Mossel, *Genetic Algorithms with Optimization Guided Operators*, STOC 2027 submission, manuscript
sha256 f89f4f77…, proof of Lemma 2, Step (i), pp.10–11): let `S ≤ 𝔽₂ⁿ` be nondegenerate and
`H := S^⊥`. Then
1. `𝔽₂ⁿ = S ⊕ H` (every `a` is uniquely `s_a + h_a` with `s_a ∈ S`, `h_a ∈ H`);
2. `H^⊥ = S`, and `H` is nondegenerate (`H ∩ H^⊥ = S^⊥ ∩ S = {0}`);
3. every `h ∈ H` is the `H`-component of exactly `|S|` vectors `a` (namely `a ∈ h + S`), so for `a`
   uniform, `h_a` is uniform on `H`;
4. `h ↦ h · h` is additive (here on all of `𝔽₂ⁿ`, in particular on `H`). -/
theorem lemma_2_step_i_decomp {n : ℕ} (S : Submodule (ZMod 2) (V n)) (hS : Nondeg S) :
    IsCompl S (orth S) ∧ orth (orth S) = S ∧ Nondeg (orth S) ∧
    (∀ h ∈ orth S, Nat.card {a : V n // a - h ∈ S} = Nat.card S) ∧
    (∀ h h' : V n, dot (h + h') (h + h') = dot h h + dot h' h') := by sorry

end GMRDiversity
