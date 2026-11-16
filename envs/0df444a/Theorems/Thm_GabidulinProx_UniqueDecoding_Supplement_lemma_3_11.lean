-- Prove2me | Theorems.Thm_GabidulinProx_UniqueDecoding_Supplement_lemma_3_11
-- name    : GabidulinProx.UniqueDecoding.Supplement.lemma_3_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:43:34.162123+00:00
-- url     : https://prove2.me/theorems/369d08dc-1c40-42ac-86d4-fc86382689e7
-- title:
--   Lemma 3.11 — $\Lambda(V)$ over four-dimensional subspaces takes every value
-- statement:
--   In the setting of Lemma 3.10 ($\mathbb F_Q$ a finite field with $Q$ elements, $F=\mathbb F_{Q^6}$, $A_V(X)=\prod_{v\in V}(X-v)$), for a $4$-dimensional $\mathbb F_Q$-subspace $V\subseteq F$ write $A_V(X)=X^{Q^4}+\Lambda(V)X^{Q^3}+(\text{lower }Q\text{-degree terms})$. Then
--
--   $$\{\Lambda(V):V\subseteq F,\ \dim_{\mathbb F_Q}V=4\}=F .$$
--
--   This is exactly the coefficient fact used by the construction in Theorems 1.4 and 3.12: every $\lambda\in F$ is the $X^{Q^3}$-coefficient of some four-dimensional subspace annihilator.
--
--   Differences from the source:
--   - encoding: $Q=q^g$ for a prime power $q$ and $g\ge1$ → an arbitrary finite field `KQ` with $Q=|KQ|$; reason: the set of numbers $q^g$ is exactly the set of prime powers, which are the finite-field sizes
--   - encoding: $\Lambda(V)$, the coefficient of the second-highest $Q$-degree term of $A_V$ → `(annihilator KQ V).coeff (Q^3)`; reason: for $\dim V=4$, $A_V$ is $Q$-linearized of $Q$-degree $4$, so that term is $X^{Q^3}$
-- source:
--   Songsong Li, Chaoping Xing, Chen Yuan, Ruiqi Zhu, Proximity Gaps for Gabidulin Codes and Applications, STOC 2027 submission #434 (October 2026), §3.3 setting p.24 and Lemma 3.11 p.26. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/434.pdf, SHA-256 8f644bcdfbdcd3478384d77d75a0f88ea116c29b14c52714f58bffb9ffda25cf

import Definitions.Def_GabidulinProx_UniqueDecoding_Supplement_Objects

namespace GabidulinProx.UniqueDecoding.Supplement

open GabidulinProx.UniqueDecoding

/-- Lemma 3.11, p.26: in the setting of Lemma 3.10 (`finrank_{F_Q} F = 6`), the coefficient
`Λ(V)` of `X^(Q^3)` in the subspace annihilator of a 4-dimensional `F_Q`-subspace `V` takes
every value: `L₄ = {Λ(V) : dim V = 4} = F`. -/
theorem lemma_3_11 {KQ F : Type*} [Field KQ] [Fintype KQ] [Field F] [Fintype F] [Algebra KQ F]
    (h6 : Module.finrank KQ F = 6) :
    {y : F | ∃ V : Submodule KQ F, Module.finrank KQ V = 4 ∧
      (annihilator KQ V).coeff (Fintype.card KQ ^ 3) = y} = Set.univ := by sorry
end GabidulinProx.UniqueDecoding.Supplement
