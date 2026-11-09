-- Prove2me | Theorems.Thm_MultiplierAssoc206_Resolution_observation_4_5
-- name    : MultiplierAssoc206.Resolution.observation_4_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:14:14.040208+00:00
-- url     : https://prove2.me/theorems/84af699e-ff22-4658-8eab-b162c6461436
-- title:
--   Strips count their partial products
-- statement:
--   Let $\mathrm{Mul}_n$ be an exact multiplier encoding, $g\ge1$ an integer, and $r$ a $g$-sparse restriction of the input bit-vectors $x,y$. For every input assignment $(x,y)$ consistent with $r$, every base $bg$ and every $t<g$ with $bg+t<2n$, the output bit $bg+t$ equals bit $t$ of the number of partial products $t_{i,j}=x_iy_j$ in the base column $i+j=bg$ that evaluate to $1$:
--   $$(xy)_{bg+t}=\mathrm{bit}_t\Big(\big|\{(i,j): i+j=bg,\ x_iy_j=1\}\big|\Big).$$
--   Thus the $g$ output bits of the strip with base $bg$ are the binary representation of this count.
--
--   The observation is how the reduction reads the perfect-matching constraints and the disagreement at column $K$ off the multipliers.
--
--   Differences from the source:
--   - encoding: the g output bits of the strip with base bg compute in binary the count, under every assignment to the unset inputs → for each t < g with bg + t < 2n, the function of output wire bg + t at every input assignment consistent with the restriction equals bit t of the count; reason: the top strip may be cut off at 2n; exactness makes every output wire equal to its function in every satisfying assignment, and when the strip is complete the bitwise statement is the binary representation
-- source:
--   Vincent Liew, Associativity of Multiplication Is Hard for Resolution, STOC 2027 submission #206 (October 2026), source.pdf SHA-256 676dcc4be9158c52d07aec1c9d48f53fa38289ed1b4dcb34b53adc70dbdd5ead, PDF p.7 (printed p.6), Observation 4.5

import Mathlib
import Definitions.Def_MultiplierAssoc206_Resolution_Multiplier

namespace MultiplierAssoc206.Resolution

/-- Observation 4.5 (Strips count their partial products), PDF p.7 (printed p.6). Output bit
`b g + t` (`t < g`, stated bit by bit since the top strip may be cut off at `2n`) is bit `t` of
the number of partial products of the base column `b g` that evaluate to `1`. -/
theorem observation_4_5 {n : ℕ} (Mn : MulEncoding n) (hMn : Mn.IsExact) (g : ℕ) (hg : 1 ≤ g)
    (r : InputRestr n) (hr : IsGSparse g r) (x y : Fin n → Bool)
    (hxy : ConsistentInputs r x y) (b t : ℕ) (ht : t < g) (hk : b * g + t < 2 * n) :
    Mn.fn (Mn.out ⟨b * g + t, hk⟩) x y = Nat.testBit (columnCount x y (b * g)) t := by sorry

end MultiplierAssoc206.Resolution
