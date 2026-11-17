-- Prove2me | Theorems.Thm_ModFormPIR_Supplement_theorem_6_1
-- name    : ModFormPIR.Supplement.theorem_6_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T06:48:49.583598+00:00
-- url     : https://prove2.me/theorems/17adec23-3d39-4c4d-82c1-62ca59ea32ce
-- title:
--   Theorem 6.1 — the two-server scheme of Fig. 4 on $2^d$ records in $\mathbb F_p$: correct, private, $O(d2^d)$ preprocessing, at most $2^{H_2(1/4)(d+1)}$ elements read
-- statement:
--   For every integer $d\ge2$ with $d\equiv2\pmod4$ and every odd prime $p>d$, the two-server PIR scheme of Fig. 4 operates over every database of $2^d$ records in $\mathbb F_p$ with information-theoretic security, and:
--
--   1. **correctness:** for every database $\mathrm{DB}$, index $i\in\mathbb F_2^d$ and randomness $r\in\mathbb F_2^d$, Reconstruct returns $\mathrm{DB}_i$;
--   2. **privacy:** for each server $t\in\{0,1\}$ and every index $i$, the query $qu_t$ is uniform on $\mathbb F_2^d$ when $r$ is;
--   3. **storage:** each server stores the truth table of $f_t$, i.e. $2^d$ elements of $\mathbb F_p$, computed from the database in $O(d2^d)$ operations over $\mathbb F_p$;
--   4. **upload:** each query is an element of $\mathbb F_2^d$, i.e. $d$ bits;
--   5. **reads:** to answer a query, each server reads and sends back the entries $\mathrm{Table}_t[qu_t+w]$, $w\in\mathcal W$, at most
--
--   $$2^{H_2(1/4)(d+1)}$$
--
--   elements of $\mathbb F_p$, where $H_2$ is the binary entropy function.
--
--   The constant in $O(d2^d)$ is absolute. This scheme, combined with the database-splitting step of Section 9.2, gives the two-server half of Main Theorem 5.2.
--
--   **Formalization Note** The scheme is the one defined in `ModFormPIR.Supplement.Fig4`. "Operations over $\mathbb F_p$" are gates (input, constant, sum, product) of a straight-line program over $\mathbb F_p$, the base mission's `Gate`/`ComputesBy`; the statement asks for one constant $C$ such that, for all admissible $d,p$ and both servers, a program of at most $C\cdot d\cdot2^d$ gates outputs the whole table. Storage and upload sizes hold by the types (a table is a function on $\mathbb F_2^d$, a query an element of $\mathbb F_2^d$).
--
--   Differences from the source:
--   - reading: there is a two-server PIR scheme … (the scheme is Fig. 4: 'we show that Fig. 4’s PIR scheme proves') → the explicit scheme of Fig. 4 (fig4Table, fig4Query, decSet, fig4Record), with correctness for every DB, i, r and privacy as uniformity of each qu_t; reason: the section proves the theorem for this scheme; correctness with probability 1 is correctness for every r
--   - reading: computed from the database in O(d2^d) operations over F_p → for one absolute C: a straight-line program over ZMod p (base Gate/ComputesBy) with at most C·d·2^d gates computes Table_t from DB; reason: operations over F_p are field operations; the constant is absolute (§6.3: 2^d sign multiplications and one Walsh–Hadamard transform)
--   - encoding: each server stores 2^d elements of F_p; the user uploads d bits → by type: Table_t is a function on Fin d → ZMod 2 and a query is an element of Fin d → ZMod 2; reason: these clauses are the sizes of the types, so no separate clause is stated
--   - encoding: reads and sends back at most 2^{H₂(1/4)(d+1)} elements → the set {qu_t + w : w ∈ 𝒲} has at most 2^{H₂(1/4)(d+1)} elements (real power), H₂ = WildeQIT.binaryEntropy; reason: server t reads exactly the entries Table_t[qu_t + w], w ∈ 𝒲 (Fig. 4, Answer)
-- source:
--   Henzinger, Ragavan, Doubly-Efficient Private Information Retrieval from Modular Forms, STOC 2027 submission (manuscript sha256 2442f3db…), Theorem 6.1, pp.22–23 (PDF pp.26–27); Fig. 4, p.23 (PDF p.27); §§6.1–6.3, pp.23–26 (PDF pp.27–30)

import Mathlib
import Definitions.Def_ModFormPIR_Expansion
import Definitions.Def_WildeQIT_binaryEntropy
import Definitions.Def_ModFormPIR_Supplement_Fig4

set_option autoImplicit false

namespace ModFormPIR

namespace Supplement

/-- **Theorem 6.1**, pp.22–23 (PDF pp.26–27), with Fig. 4 and §6.1–6.3, pp.23–26. Henzinger, Ragavan,
*Doubly-Efficient Private Information Retrieval from Modular Forms*, STOC 2027 submission (manuscript sha256
2442f3db…). For every integer `d ≥ 2` with `d ≡ 2 (mod 4)` and every odd prime `p > d`, the two-server scheme of
Fig. 4 on `2^d` records in `𝔽_p` is correct and information-theoretically private; each server's table is
computed from the database in `O(d 2^d)` operations over `𝔽_p`; and each server reads and sends back at most
`2^{H₂(1/4)(d+1)}` elements of its table.

**Formalization Note.** The scheme is the explicit one of Fig. 4 (`fig4Table`, `fig4Query`, `decSet`,
`fig4Record`), servers `t ∈ 𝔽₂`. Correctness: `Reconstruct` returns `DB_i` for every database, index and
randomness `r`. Privacy: under uniform `r`, `qu_t` is uniform on `𝔽₂^d` whatever the index. Each table is a
function on `𝔽₂^d` (`2^d` elements of `𝔽_p`), and each query an element of `𝔽₂^d` (`d` bits), by type.
"Operations over `𝔽_p`" are gates of a straight-line program (the base mission's `Gate`, `ComputesBy`), and
`O(d 2^d)` is `C·d·2^d` for one absolute `C`. The elements read by server `t` are `Table_t[qu_t + w]`,
`w ∈ 𝒲`; `H₂` is the base-2 binary entropy `WildeQIT.binaryEntropy`. -/
theorem theorem_6_1 :
    ∃ C : ℕ, ∀ d p : ℕ, 2 ≤ d → d % 4 = 2 → p.Prime → Odd p → d < p →
      (∀ (DB : (Fin d → ZMod 2) → ZMod p) (i r : Fin d → ZMod 2),
        fig4Record p DB i r = DB i) ∧
      (∀ (i : Fin d → ZMod 2) (t : ZMod 2),
        (PMF.uniformOfFintype (Fin d → ZMod 2)).map (fun r => fig4Query r i t) =
          PMF.uniformOfFintype (Fin d → ZMod 2)) ∧
      (∀ t : ZMod 2, ∃ (gs : List (Gate (ZMod p) (Fin d → ZMod 2))) (out : (Fin d → ZMod 2) → ℕ),
        gs.length ≤ C * d * 2 ^ d ∧ ComputesBy gs out fun DB x => fig4Table p t DB x) ∧
      (∀ (r i : Fin d → ZMod 2) (t : ZMod 2),
        ((((decSet d).image fun w => fig4Query r i t + w).card : ℕ) : ℝ) ≤
          (2 : ℝ) ^ (WildeQIT.binaryEntropy (1 / 4) * ((d : ℝ) + 1))) := by sorry

end Supplement

end ModFormPIR
