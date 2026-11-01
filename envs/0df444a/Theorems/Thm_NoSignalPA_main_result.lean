-- Prove2me | Theorems.Thm_NoSignalPA_main_result
-- name    : NoSignalPA.main_result
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T16:06:09.486431+00:00
-- url     : https://prove2.me/theorems/233c5651-fb24-47ee-a702-3c894fc5713a
-- title:
--   Main result — for almost all hash functions $h$, the key $h(\mathbf a)$ is secure against every nonsignaling eavesdropper, eq. (5)
-- statement:
--   Let $N_r,N_s\ge0$ and pick $h:\{0,1\}^{N_r}\to\{0,1\}^{N_s}$ uniformly at random. Call $h$ **secure** if for every choice of Eve's input and output sets $Z,E$, every $(N_r+2)$-partite nonsignaling box $P_{\mathbf a,\mathbf b,e|\mathbf x,\mathbf y,z}$ (Alice's $N_r$ systems, Bob as one system, Eve as one system), every input $\mathbf y$ of Bob and every input $z_0$ of Eve, the key $\mathbf k=h(\mathbf a)$ produced at Alice's input $\mathbf x=\mathbf 0$ satisfies
--
--   $$
--   \sum_{\mathbf k}\ \sup_{z}\ \sum_{e}\Bigl|P_{\mathbf k,e|\mathbf x=\mathbf 0,z}-2^{-N_s}P_{e|z}\Bigr|\ \le\ \sqrt{2^{\,N_s+\sqrt{N_r}}}\ \langle\mathrm{CHSH}|^{\otimes N_r}|P_{\mathbf a,\mathbf b|\mathbf x,\mathbf y}\rangle .\qquad(5)
--   $$
--
--   Then
--
--   $$
--   \Pr_h\{h\ \text{is not secure}\}<2\exp\bigl(5N_r-2^{\sqrt{N_r}}/4\bigr).
--   $$
--
--   The left side of (5) measures how well an eavesdropper limited only by no signaling can distinguish the real key from a uniform key independent of her system; the right side is small when Alice and Bob's correlations violate the CHSH inequality strongly. So almost every fixed hash function, chosen before the boxes and known to everybody, turns sufficiently nonlocal raw keys into a universally composable secret key. For $N_r\le128$ the bound on the probability is at least $1$, as on the page.
--
--   Differences from the source:
--   - reading: for almost all h and any (Nr + 2)-partite nonsignaling P, (5) holds → one set of good h, IsSecure h, fixed before the box: IsSecure quantifies over every box; reason: the sentence admits the swapped order (for each P, most h), which is strictly weaker; the stronger reading is the one the proof gives (p. 3: every h satisfying (6) works for every P)
--   - reading: (Nr + 2)-partite nonsignaling distribution P_{a,b,e|x,y,z} → IsNonsignaling: for each of Alice's Nr systems, Bob (one system) and Eve, summing out that party's output leaves a quantity independent of that party's input; reason: pp. 1–2 define no signaling as 'the marginals only depend on their corresponding observables', with Bob's systems as one; the single-party conditions imply those for every subset of parties
--   - generalization: Eve's input z and output e, with Σ_e and max_z (no alphabets fixed) → Z and E arbitrary types in a universe u, P x y z a PMF on (a, b, e), max_z as ⨆ and Σ_e as tsum in ℝ≥0∞; reason: every finite alphabet is such a type and then ⨆ is the maximum and tsum the finite sum; the security predicate quantifies over more boxes, so it specializes to the paper's
--   - reading: P_{k,e|x=0,z}, P_{e|z} and P_{a,b|x,y} (inputs of other parties not shown) → key and Eve marginals read at x = 0 and any Bob input y; P_{a,b|x,y} read at any Eve input z₀; IsSecure quantifies over y and z₀; reason: under no signaling these marginals do not depend on the omitted inputs; quantifying over them is the stronger reading
-- source:
--   Masanes, Universally-composable privacy amplification from causality constraints, arXiv:0807.2158v4, Main result, eq. (5), p.2, with the definition of 'almost all' on p.2

import Mathlib
import Definitions.Def_NoSignalPA_IsSecure
import Definitions.Def_OAI_Probability_ThorpCompatibility_PermutationProbability

namespace NoSignalPA

/-- **Main result: almost every hash function `h` yields a key secure against every nonsignaling
eavesdropper.**
Ll. Masanes, *Universally-composable privacy amplification from causality constraints*,
arXiv:0807.2158v4, Main result, eq. (5), p. 2 (PDF p. 2): "For almost all functions `h : {0,1}^{Nr} →
{0,1}^{Ns}` and any `(Nr + 2)`-partite nonsignaling distribution `P_{a,b,e|x,y,z}`, the random
variable `k = h(a)` satisfies `Σ_k max_z Σ_e |P_{k,e|x=0,z} − 2^{−Ns} P_{e|z}| ≤
√2^{Ns+√Nr} ⟨CHSH|^{⊗Nr} |P_{a,b|x,y}⟩`, (5)", with "almost all" defined on p. 2: "when randomly
picking a function h with uniform distribution over all functions h : {0,1}^{Nr} → {0,1}^{Ns} then
the probability that h does not have that particular property is lower than
`2 exp(5Nr − 2^{√Nr}/4)`".

For all `Nr, Ns`: the probability that a uniformly random `h` fails `IsSecure` (the bound (5) for
every nonsignaling box, every Eve alphabet and every choice of the marginals' free inputs) is less
than `2 exp(5Nr − 2^{√Nr}/4)`.

**Formalization Note.** The good set of `h` is fixed before the box: `IsSecure h` quantifies over
all boxes. There is no hypothesis relating `Ns` and `Nr`. For `Nr ≤ 128` the bound is at least 1,
as on the page. -/
theorem main_result.{u} (Nr Ns : ℕ) :
    OAI.ThorpCompatibility.uniformProbability (fun h : Str Nr → Str Ns => ¬ IsSecure.{u} h)
      < 2 * Real.exp (5 * Nr - (2 : ℝ) ^ Real.sqrt Nr / 4) := by sorry

end NoSignalPA
