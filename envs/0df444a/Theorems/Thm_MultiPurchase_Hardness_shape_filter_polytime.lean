-- Prove2me | Theorems.Thm_MultiPurchase_Hardness_shape_filter_polytime
-- name    : MultiPurchase.Hardness.shape_filter_polytime
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-11-03T03:52:50.255222+00:00
-- url     : https://prove2.me/theorems/df866023-a3dc-4b5a-b7ac-3ffbb0776a9d
-- title:
--   BundleMVL-2 NP checker, step 1: the shape-and-sign filter is polynomial-time computable
-- statement:
--   Let words over the alphabet $\Sigma = \{0,1,-,\mathrm{sep}\} \uplus \{0,1\} \uplus \{\#\}$ be checker inputs. For an integer list $c$ and a bit list $d$, write $\langle c\#d\rangle$ for the word `chkWord c d`: the binary code of $c$ (each integer as an optional minus sign, its binary digits least significant first without leading zeros, and a separator), the symbol $\#$, then the bits of $d$.
--
--   **Claim.** The filter
--   $$F_{\mathrm{shape}}(u) = \begin{cases} u & \text{if } u = \langle c\#d\rangle \text{ for some } c, d \text{ with } \mathrm{ShapeOK}(c,d),\\ \varepsilon & \text{otherwise}\end{cases}$$
--   is computable in polynomial time by a Cook Turing machine. Here $\mathrm{ShapeOK}(c,d)$ says: $n = c_0 \ge 0$; $c$ has exactly $2(2n + n(n-1)/2 + 2) + 1$ entries; $|d| = n$; the numerators of the revenues $r_0,\dots,r_{n-1}$ are positive; the numerators of all weights $V_{\{i\}}$, $V_{\{i,j\}}$ are nonnegative; and the numerator of $v_0$ is positive.
--
--   This is the first of three polynomial-time checks whose composition decides the checking language of the BundleMVL-2 decision problem; it recognizes the syntax of an instance code together with an $n$-bit certificate and the sign conditions of a well-formed instance.
--
--   **Formalization Note.** `ShapeOK` and `chkWord` are from `Definitions.Def_MultiPurchase_Hardness_Checker`; the `if` is classical.
-- source:
--   Tulabandhula, Sinha, Karra & Patidar, Multi-Purchase Behavior: Modeling, Estimation and Optimization, arXiv:2006.08055v2, p. 17, Theorem 1 (membership half: the decision version of (5) is in NP), eq. (4); polynomial-time computability as in S. Cook, The P versus NP problem (Clay Mathematics Institute), §1 and Definition 3

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_ProjSchedTW_Complexity_Encoding
import Definitions.Def_MultiPurchase_Hardness_Model
import Definitions.Def_MultiPurchase_Hardness_Checker

namespace MultiPurchase.Hardness

open CookPvsNP ProjSchedTW.Complexity

open Classical in
theorem shape_filter_polytime :
    PolyTimeComputable (fun u : List (Option (BSym ⊕ Bool)) =>
      if ∃ c d, u = chkWord c d ∧ ShapeOK c d then u else []) := by sorry

end MultiPurchase.Hardness
