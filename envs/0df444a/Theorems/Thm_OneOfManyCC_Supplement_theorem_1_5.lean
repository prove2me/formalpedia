-- Prove2me | Theorems.Thm_OneOfManyCC_Supplement_theorem_1_5
-- name    : OneOfManyCC.Supplement.theorem_1_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:21:59.576764+00:00
-- url     : https://prove2.me/theorems/4f544149-4337-44c6-b690-3c999fe7e152
-- title:
--   Theorem 1.5 — $D(f)\le D(\mathrm{Agr}_2(f))+\lceil\log_2 n\rceil+1$ and $L(f)\le 2n\,L(\mathrm{Agr}_2(f))$
-- statement:
--   Let $f:\{0,1\}^n\to\{0,1,*\}$ be a partial function with $|f^{-1}(0)|\ge 2$ and $|f^{-1}(1)|\ge 2$, and let $\mathrm{Agr}_2(f)$ be its 1-out-of-2 agreement function on $2n$ bits. Write $D$ and $L$ for the minimum depth and the minimum number of leaves of a De Morgan formula computing a partial function. Then
--   $$D(f)\le D(\mathrm{Agr}_2(f))+\lceil\log_2 n\rceil+1,\qquad L(f)\le 2n\,L(\mathrm{Agr}_2(f)).$$
--
--   Computing the common value of two distinct inputs from the same side of $f$ is thus almost as hard as computing $f$, both in depth (an explicit additive loss) and in size (an explicit factor $2n$).
--
--   **Formalization Note** $f$ is `(Fin n → Bool) → Option Bool`; formulas for $\mathrm{Agr}_2(f)$ read all $2n$ bits, indexed by `Fin n ⊕ Fin n`. $\lceil\log_2 n\rceil$ is `Nat.clog 2 n`.
--
--   Differences from the source:
--   - encoding: partial f : {0,1}ⁿ → {0,1,∗} → (Fin n → Bool) → Option Bool, none = ∗; reason: the same partial functions
--   - encoding: the kn = 2n input bits of Agr₂(f) → Fin n ⊕ Fin n; reason: a relabelling of the 2n bits; formulas over them have the same depth and leaf count
--   - encoding: De Morgan formula; D(f), L(f) as minima → the published Formula over DMLeaf (literals of both polarities and constants); sInf over ℕ; reason: the sets are nonempty for finitely many bits (proved in the verification file), so sInf is the minimum
--   - encoding: ⌈log₂ n⌉ → Nat.clog 2 n; reason: equal for n ≥ 1; the hypotheses force n ≥ 2
-- source:
--   Chukhin, Kulikov, Mihajlin, Smal, Solving One of Many Instances Is Almost as Hard as Solving One, STOC 2027 submission (manuscript sha256 5d4d41dd…), Theorem 1.5, p.2 (PDF p.3); restated p.8, proof pp.8–9 (PDF pp.9–10)

import Mathlib
import Definitions.Def_OneOfManyCC_Supplement_DeMorgan
import Definitions.Def_OneOfManyCC_Supplement_Agr2

namespace OneOfManyCC.Supplement

/-- **Theorem 1.5** (1-out-of-2 agreement).
Chukhin, Kulikov, Mihajlin, Smal, *Solving One of Many Instances Is Almost as Hard as Solving One*, STOC 2027 submission (manuscript sha256 5d4d41dd…), Theorem 1.5, p.2 (restated p.8, proof pp.8–9):
"For every partial f : {0, 1}ⁿ → {0, 1, ∗} with |f⁻¹(0)|, |f⁻¹(1)| ≥ 2,
D(f) ≤ D(Agr2(f)) + ⌈log2 n⌉ + 1, L(f) ≤ 2n L(Agr2(f))."

**Formalization Note.** A partial function is `(Fin n → Bool) → Option Bool` (`none` = `∗`).
`D`, `L` are minimum depth and minimum leaf count of De Morgan formulas (literals of both
polarities and constants as leaves); for `Agr₂(f)` the formulas are over all `2n` bits
`Fin n ⊕ Fin n`. `⌈log₂ n⌉` is `Nat.clog 2 n`. Both conclusions are stated with the exact constants. -/
theorem theorem_1_5 (n : ℕ) (f : (Fin n → Bool) → Option Bool)
    (h0 : 2 ≤ (Finset.univ.filter (fun x => f x = some false)).card)
    (h1 : 2 ≤ (Finset.univ.filter (fun x => f x = some true)).card) :
    D f ≤ D (Agr2 f) + Nat.clog 2 n + 1 ∧ L f ≤ 2 * n * L (Agr2 f) := by sorry

end OneOfManyCC.Supplement
