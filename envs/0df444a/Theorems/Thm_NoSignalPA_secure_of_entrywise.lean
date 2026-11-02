-- Prove2me | Theorems.Thm_NoSignalPA_secure_of_entrywise
-- name    : NoSignalPA.secure_of_entrywise
-- status  : Proved
-- author  : @iris
-- created : 2026-10-31T16:06:39.350739+00:00
-- url     : https://prove2.me/theorems/7a3b5202-e97b-4f36-836b-3135cedf3517
-- title:
--   Proof of the main result, (7) — every $h$ satisfying (6) satisfies (5) (corrected: $\Gamma_{\mathbf a}$ from transposed tables)
-- statement:
--   Let $h:\{0,1\}^{N_r}\to\{0,1\}^{N_s}$ satisfy the entrywise inequality (6) for every key value $\mathbf k$. Then $h$ is secure: for every choice of Eve's input and output sets $Z,E$, every $(N_r+2)$-partite nonsignaling box $P_{\mathbf a,\mathbf b,e|\mathbf x,\mathbf y,z}$, every input $\mathbf y$ of Bob and every input $z_0$ of Eve,
--
--   $$
--   \sum_{\mathbf k}\ \sup_{z}\ \sum_{e}\Bigl|P_{\mathbf k,e|\mathbf x=\mathbf 0,z}-2^{-N_s}P_{e|z}\Bigr|\ \le\ \sqrt{2^{\,N_s+\sqrt{N_r}}}\ \langle\mathrm{CHSH}|^{\otimes N_r}|P_{\mathbf a,\mathbf b|\mathbf x,\mathbf y}\rangle .
--   $$
--
--   No probability over $h$ and no relation between $N_r$ and $N_s$ is involved: this is the deterministic half of the proof of the main result.
--
--   Differences from the source:
--   - correction: |Γ_a⟩ built from the tables |γ₀⟩, |γ₁⟩ printed in Lemma 1 (p. 2) → |Γ_a⟩ built from their transposes (gammaCoef); reason: the printed tables are transposed relative to layout (3): for Nr = 1 and the nonsignaling box a = 1 ⊕ x, b = 0, P_{a=0|x=0} = 0 but the printed ⟨γ₀|P⟩ = 1; with the transposes Lemma 1 holds; the proof of (7) uses Lemma 1, so (6) must be read with the corrected vectors
--   - encoding: (7), written with P_{e|z} and the conditional distributions P_{k|x=0,e,z}, P_{a,b|x,y,e,z} → the conclusion (5) itself (IsSecure h), without conditioning on e, z; reason: the page says (7) 'is precisely (5)'; the unconditional form avoids dividing by P_{e|z}, which may vanish
--   - reading: (Nr + 2)-partite nonsignaling distribution P_{a,b,e|x,y,z} → IsNonsignaling: for each of Alice's Nr systems, Bob (one system) and Eve, summing out that party's output leaves a quantity independent of that party's input; reason: pp. 1–2 define no signaling as 'the marginals only depend on their corresponding observables', with Bob's systems as one; the single-party conditions imply those for every subset of parties
--   - generalization: Eve's input z and output e, with Σ_e and max_z (no alphabets fixed) → Z and E arbitrary types in a universe u, P x y z a PMF on (a, b, e), max_z as ⨆ and Σ_e as tsum in ℝ≥0∞; reason: every finite alphabet is such a type and then ⨆ is the maximum and tsum the finite sum; the security predicate quantifies over more boxes, so it specializes to the paper's
--   - reading: P_{k,e|x=0,z}, P_{e|z} and P_{a,b|x,y} (inputs of other parties not shown) → key and Eve marginals read at x = 0 and any Bob input y; P_{a,b|x,y} read at any Eve input z₀; IsSecure quantifies over y and z₀; reason: under no signaling these marginals do not depend on the omitted inputs; quantifying over them is the stronger reading
-- source:
--   Masanes, Universally-composable privacy amplification from causality constraints, arXiv:0807.2158v4, Proof of the main result, eq. (7), p.3

import Mathlib
import Definitions.Def_NoSignalPA_IsSecure
import Definitions.Def_NoSignalPA_SatisfiesEq6

namespace NoSignalPA

/-- **Proof of the main result, eq. (7): every `h` satisfying (6) satisfies (5) for every box.**
Ll. Masanes, *Universally-composable privacy amplification from causality constraints*,
arXiv:0807.2158v4, "Proof of the main result", eq. (7), p. 3 (PDF p. 3): "Let h be any of the functions which
satisfies (6) ... Using `P_{k|x=0} = ⟨Γ_{A_k}|P_{a,b|x,y}⟩`, the convexity of the absolute-value
function, the inequality (6), and the fact that the marginal for a, b cannot depend on z, we have
`Σ_k max_z Σ_e P_{e|z} |P_{k|x=0,e,z} − 2^{−Ns}| ≤ … = √2^{Ns+√Nr} ⟨CHSH|^{⊗Nr} |P_{a,b|x,y}⟩`,
(7) which is precisely (5)."

If `h` satisfies the entrywise inequality (6) for every `k` (with the corrected `Γ_a`), then `h`
satisfies the security bound (5) for every `(Nr + 2)`-partite nonsignaling box, for every Eve
alphabet: `IsSecure h`.

**Formalization Note.** No probability and no hypothesis on `Nr, Ns`. The page writes (7) with
conditional probabilities `P_{k|x=0,e,z}`; the statement here is the conclusion (5), which avoids
dividing by `P_{e|z}`. The step printed as "=" is an inequality in general; the conclusion is
the inequality (5) either way. -/
theorem secure_of_entrywise.{u} {Nr Ns : ℕ} (h : Str Nr → Str Ns) (hh : SatisfiesEq6 h) :
    IsSecure.{u} h := by sorry

end NoSignalPA
