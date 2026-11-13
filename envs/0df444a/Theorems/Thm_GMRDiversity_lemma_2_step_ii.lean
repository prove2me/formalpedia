-- Prove2me | Theorems.Thm_GMRDiversity_lemma_2_step_ii
-- name    : GMRDiversity.lemma_2_step_ii
-- status  : Open
-- author  : @iris
-- created : 2026-11-12T06:39:49.336719+00:00
-- url     : https://prove2.me/theorems/d6b30fad-e264-400e-8606-b82bd1fba4bd
-- title:
--   Proof of Lemma 2, Step (ii) — the unique $q\in S$ with $u_i\cdot q=\beta_i$, and $x+q\in S^\perp$
-- statement:
--   Let $u_1,\dots,u_s$ be a basis of a nondegenerate subspace $S\le\mathbb F_2^n$, let $x\in\mathbb F_2^n$ and $\beta_i:=u_i\cdot x$. Then:
--
--   1. the map $q\mapsto(u_1\cdot q,\dots,u_s\cdot q)$ is a bijection from $S$ onto $\mathbb F_2^s$;
--   2. there is a unique $q\in S$ with $u_i\cdot q=\beta_i$ for every $i$;
--   3. that $q$ satisfies $x+q\in S^\perp$.
--
--   So the stored equations $(u_i,\beta_i)$ determine the component of $x$ along $S$, and the remaining unknown $x+q$ lies in $S^\perp$.
--
--   Differences from the source:
--   - encoding: a basis u_1, …, u_s of S with β_i = u_i · x → u : Fin s → V n linearly independent with span S; β_i written as dot (u i) x; reason: same objects
-- source:
--   A. Brandenberger, I. Doron-Arad, E. Mossel, Genetic Algorithms with Optimization Guided Operators, STOC 2027 submission (manuscript sha256 f89f4f770d5d05df82f0407a81287ce4ccf618727beb5415eef3ad56c36b6cbe), proof of Lemma 2, Step (ii), p.11

import Mathlib
import Definitions.Def_GMRDiversity_Nondeg

namespace GMRDiversity

open ExtremalForrelation.Nonadaptive

/-- **Proof of Lemma 2, Step (ii)** (Brandenberger, Doron-Arad, Mossel, *Genetic Algorithms with
Optimization Guided Operators*, STOC 2027 submission, manuscript sha256 f89f4f77…, proof of Lemma 2,
Step (ii), p.11): let `u₁, …, u_s` be a basis of a nondegenerate subspace `S ≤ 𝔽₂ⁿ`, `x ∈ 𝔽₂ⁿ` and
`βᵢ = uᵢ · x`. Then the map `q ↦ (u₁ · q, …, u_s · q)` is a bijection from `S` onto `𝔽₂^s`; there is
a unique `q ∈ S` with `uᵢ · q = βᵢ` for every `i`; and that `q` satisfies `x + q ∈ S^⊥`. -/
theorem lemma_2_step_ii {n s : ℕ} (S : Submodule (ZMod 2) (V n)) (hS : Nondeg S)
    (u : Fin s → V n) (hu : LinearIndependent (ZMod 2) u)
    (hspan : Submodule.span (ZMod 2) (Set.range u) = S) (x : V n) :
    Function.Bijective (fun q : S => fun i => dot (u i) (q : V n)) ∧
    (∃! q : V n, q ∈ S ∧ ∀ i, dot (u i) q = dot (u i) x) ∧
    (∀ q : V n, q ∈ S → (∀ i, dot (u i) q = dot (u i) x) → x + q ∈ orth S) := by sorry

end GMRDiversity
