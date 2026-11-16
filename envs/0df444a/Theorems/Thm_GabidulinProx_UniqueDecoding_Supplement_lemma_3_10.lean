-- Prove2me | Theorems.Thm_GabidulinProx_UniqueDecoding_Supplement_lemma_3_10
-- name    : GabidulinProx.UniqueDecoding.Supplement.lemma_3_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:43:05.727587+00:00
-- url     : https://prove2.me/theorems/b40f391a-8474-4483-984f-a19986cfaabf
-- title:
--   Lemma 3.10 — $\Lambda(U)$ over two-dimensional subspaces takes every value
-- statement:
--   Let $\mathbb F_Q$ be a finite field with $Q$ elements and let $F=\mathbb F_{Q^6}$ be an extension of degree $6$. For an $\mathbb F_Q$-subspace $U\subseteq F$ let $A_U(X)=\prod_{u\in U}(X-u)$ be its subspace annihilator. If $\dim_{\mathbb F_Q}U=2$ then $A_U(X)=X^{Q^2}+\Lambda(U)X^Q+\mu X$, and $\Lambda(U)$ is the coefficient of the second-highest $Q$-degree term. Then
--
--   $$\{\Lambda(U):U\subseteq F,\ \dim_{\mathbb F_Q}U=2\}=F .$$
--
--   This coefficient fact feeds Lemma 3.11 and the counterexample of Theorems 1.4 and 3.12.
--
--   Differences from the source:
--   - encoding: $Q=q^g$ for a prime power $q$ and $g\ge1$ → an arbitrary finite field `KQ` with $Q=|KQ|$; reason: the set of numbers $q^g$ is exactly the set of prime powers, which are the finite-field sizes
--   - encoding: $\Lambda(U)$, the coefficient of the second-highest $Q$-degree term of $A_U$ → `(annihilator KQ U).coeff Q`, with the published monic annihilator $\prod_{u\in U}(X-u)$; reason: for $\dim U=2$, $A_U$ is $Q$-linearized of $Q$-degree $2$, so that term is $X^Q$
-- source:
--   Songsong Li, Chaoping Xing, Chen Yuan, Ruiqi Zhu, Proximity Gaps for Gabidulin Codes and Applications, STOC 2027 submission #434 (October 2026), §3.3 setting and Lemma 3.10 p.24; proof pp.24–26. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/434.pdf, SHA-256 8f644bcdfbdcd3478384d77d75a0f88ea116c29b14c52714f58bffb9ffda25cf

import Definitions.Def_GabidulinProx_UniqueDecoding_Supplement_Objects

namespace GabidulinProx.UniqueDecoding.Supplement

open GabidulinProx.UniqueDecoding

/-- Lemma 3.10, p.24: let `F_Q = KQ` be a finite field with `Q = |KQ|` and `F` a degree-6
extension. The coefficient `Λ(U)` of `X^Q` (the second-highest `Q`-degree term) in the
subspace annihilator `A_U = ∏_{u∈U}(X-u)` of a 2-dimensional `F_Q`-subspace `U` takes every
value: `L₂ = {Λ(U) : dim U = 2} = F`. -/
theorem lemma_3_10 {KQ F : Type*} [Field KQ] [Fintype KQ] [Field F] [Fintype F] [Algebra KQ F]
    (h6 : Module.finrank KQ F = 6) :
    {y : F | ∃ U : Submodule KQ F, Module.finrank KQ U = 2 ∧
      (annihilator KQ U).coeff (Fintype.card KQ) = y} = Set.univ := by sorry
end GabidulinProx.UniqueDecoding.Supplement
