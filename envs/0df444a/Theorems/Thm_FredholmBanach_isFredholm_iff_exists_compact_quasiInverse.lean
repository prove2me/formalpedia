-- Prove2me | Theorems.Thm_FredholmBanach_isFredholm_iff_exists_compact_quasiInverse
-- name    : FredholmBanach.isFredholm_iff_exists_compact_quasiInverse
-- status  : Open
-- author  : @Mazecto
-- created : 2026-10-09T15:41:17.160717+00:00
-- url     : https://prove2.me/theorems/470abbf0-eed0-421b-99f8-c82405a64d24
-- title:
--   Atkinson's theorem: Fredholm operators are the operators invertible modulo compact operators
-- statement:
--   Let $\mathbb{K}$ be $\mathbb{R}$ or $\mathbb{C}$ and let $E$, $F$ be Banach spaces over $\mathbb{K}$. A bounded linear map $u:E\to F$ is a Fredholm operator if and only if there is a bounded linear map $v:F\to E$ such that both
--   $$1_E-v\circ u\quad\text{and}\quad 1_F-u\circ v$$
--   are compact operators (each maps some neighbourhood of $0$ into a compact set).
--
--   This identifies the Fredholm operators with the operators that are invertible modulo the compact operators.
-- source:
--   N. Bourbaki, Théories spectrales, Chapitres III à V, Springer (2023), https://doi.org/10.1007/978-3-031-19505-1, Chapitre III, § 5, n° 3, Corollaire 1, p. TS III.74 (stated there for separated locally convex spaces)

import Definitions.Def_FredholmBanach_Setting

namespace FredholmBanach

open Topology

/-- Bourbaki, *Théories spectrales*, III, § 5, n° 3, Corollaire 1 (TS III.74), for Banach spaces
(Atkinson's theorem): `u` is Fredholm if and only if there is `v : F →L[𝕜] E` such that
`1_E - v ∘ u` and `1_F - u ∘ v` are compact operators. -/
theorem isFredholm_iff_exists_compact_quasiInverse {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
    (u : E →L[𝕜] F) :
    u.IsFredholm ↔ ∃ v : F →L[𝕜] E,
      IsCompactOperator (ContinuousLinearMap.id 𝕜 E - v.comp u) ∧
        IsCompactOperator (ContinuousLinearMap.id 𝕜 F - u.comp v) := by sorry

end FredholmBanach
