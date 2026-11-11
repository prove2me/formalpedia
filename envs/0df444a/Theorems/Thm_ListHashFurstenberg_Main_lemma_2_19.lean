-- Prove2me | Theorems.Thm_ListHashFurstenberg_Main_lemma_2_19
-- name    : ListHashFurstenberg.Main.lemma_2_19
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:09:38.801142+00:00
-- url     : https://prove2.me/theorems/9e64f504-c797-4df9-86bd-a463b36ffa4f
-- title:
--   Lemma 2.19 — a random surjective map to $\mathbb F_q^{2t}$ is injective on a set of size $q^t$ with probability at least $1/2$
-- statement:
--   Let $F$ be a finite field with $q=|F|$ elements, $V$ any vector space over $F$ (of any dimension, possibly infinite), $t\ge0$ an integer, and let $f:V\to F^{2t}$ be a uniformly random surjective linear map. For every finite set $B\subseteq V$ with $|B|\le q^t$,
--
--   $$\Pr_f\big[\,|f(B)|=|B|\,\big]\ge\frac12.$$
--
--   This is the converse of the birthday paradox for linear maps, and it is the step of Theorem 2.20 that compresses the ambient dimension.
--
--   Differences from the source:
--   - encoding: $\mathbb F_q$ with $q$ a prime power → an arbitrary finite field $F$ with $q=|F|$; reason: every finite field has prime-power order and every prime power is the order of a finite field, so the instances are the same.
--   - encoding: a uniformly random surjective linear map on an arbitrary vector space $V$ → the law `probSurj`: images of a fixed basis independent and uniform (Haar measure on $\mathrm{Hom}_F(V,F^{2t})$), conditioned on surjectivity; reason: on finite-dimensional $V$ it is uniform counting over surjections, and on infinite-dimensional $V$ it is the compact-group law the phrase denotes.
--   - encoding: sampling a surjection presupposes one exists → hypothesis that some surjective linear map $V\to F^{2t}$ exists; reason: it excludes only the case $\dim V<2t$, where the source's random map is undefined.
--   - reading: $t$ unspecified → $t$ a natural number; reason: $F_q^{2t}$ needs an integer dimension $2t$, and the lemma is applied with $t=\lceil\log_qT\rceil$.
-- source:
--   Vinayak M. Kumar, Geoffrey Mon, List Decoding, Linear Hashing, and Furstenberg over F_q, STOC 2027 submission #1578 (October 2026), PDF SHA-256 7cc3a39af88d6de0a57be33c5d8c2855020a7107b6d5e947fb47901273a80ed9, Lemma 2.19, p.19

import Mathlib
import Definitions.Def_ListHashFurstenberg_Main_SurjLaw

namespace ListHashFurstenberg.Main

open Classical in
/-- Lemma 2.19, p.19 of Kumar–Mon, STOC 2027 submission #1578 (dimension reduction). Let `V` be
a vector space over the finite field `F` (`q = |F|`) and let `f : V → F^{2t}` be a uniformly
random surjective linear map. For every set `B ⊆ V` of size at most `q^t`,
`Pr_f[|f(B)| = |B|] ≥ 1/2`. -/
theorem lemma_2_19 {F : Type*} [Field F] [Fintype F] (V : Type*) [AddCommGroup V] [Module F V]
    (t : ℕ) (hsurj : ∃ f : V →ₗ[F] (Fin (2 * t) → F), Function.Surjective f)
    (B : Finset V) (hB : B.card ≤ Fintype.card F ^ t) :
    1 / 2 ≤ probSurj F V (2 * t) (fun f => (B.image f).card = B.card) := by sorry

end ListHashFurstenberg.Main
